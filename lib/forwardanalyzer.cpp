/*
 * Cppcheck - A tool for static C/C++ code analysis
 * Copyright (C) 2007-2026 Cppcheck team.
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

#include "forwardanalyzer.h"

#include "analyzer.h"
#include "astutils.h"
#include "config.h"
#include "errorlogger.h"
#include "errortypes.h"
#include "mathlib.h"
#include "refthunk.h"
#include "settings.h"
#include "symboldatabase.h"
#include "token.h"
#include "tokenlist.h"
#include "utils.h"
#include "valueptr.h"

#include <algorithm>
#include <cassert>
#include <cstddef>
#include <cstdio>
#include <cstdint>
#include <functional>
#include <iterator>
#include <list>
#include <memory>
#include <numeric>
#include <string>
#include <tuple>
#include <type_traits>
#include <utility>
#include <vector>

namespace {
    // One way through the code: the tracked value with the state assumed on the way. The traversal
    // walks one path at a time; the others are kept aside and swapped in.
    struct Path {
        explicit Path(const ValuePtr<Analyzer>& analyzer) : analyzer(analyzer) {}
        ValuePtr<Analyzer> analyzer;
        Analyzer::Action actions;
        bool analyzeOnly{};
        bool analyzeTerminate{};
        Analyzer::Terminate terminate = Analyzer::Terminate::None;
        int branchCount = 0;
        // Nested condition-fork depth of this path; bounds the fan-out.
        int forkDepth = 0;
    };

    struct ForwardTraversal : Path {
        // Forked: the path was replaced by the paths of a fork, which are counted in the range
        enum class Progress : std::uint8_t { Continue, Break, Skip, Forked };
        ForwardTraversal(const ValuePtr<Analyzer>& analyzer, const TokenList& tokenList, ErrorLogger& errorLogger, const Settings& settings)
            : Path(analyzer), tokenList(tokenList), errorLogger(errorLogger), settings(settings)
        {}
        RefThunk<const TokenList> tokenList;
        RefThunk<ErrorLogger> errorLogger;
        RefThunk<const Settings> settings;
        std::vector<Token*> loopEnds;
        // Total forks of the traversal (shared via the fork() copy); backstop past the depth bound.
        std::shared_ptr<int> forkBudget = std::make_shared<int>(0);

        Path& path() {
            return *this;
        }

        Progress Break(Analyzer::Terminate t = Analyzer::Terminate::None) {
            if ((!analyzeOnly || analyzeTerminate) && t != Analyzer::Terminate::None)
                terminate = t;
            return Progress::Break;
        }

        // What became of the paths through a range
        struct Outcome {
            Analyzer::Action action = Analyzer::Action::None;
            int reached = 0;
            // How each path that did not reach the end stopped
            std::vector<Analyzer::Terminate> stops;

            void reach(Analyzer::Action a) {
                action |= a;
                ++reached;
            }
            void stop(Analyzer::Action a, Analyzer::Terminate t) {
                action |= a;
                stops.push_back(t);
            }
            // The paths that stopped in a block of the range stopped in the range. If another path
            // covers the code they did not walk, only an escape or a changed value counts.
            void add(const Outcome& block, bool covered) {
                action |= block.action;
                for (Analyzer::Terminate t : block.stops) {
                    if (covered && t != Analyzer::Terminate::Escape && t != Analyzer::Terminate::Modified)
                        t = Analyzer::Terminate::None;
                    stops.push_back(t);
                }
            }
            bool hasEscape() const {
                return std::find(stops.cbegin(), stops.cend(), Analyzer::Terminate::Escape) != stops.cend();
            }
            bool allEscape() const {
                return reached == 0 && !stops.empty() &&
                       std::count(stops.cbegin(), stops.cend(), Analyzer::Terminate::Escape) == static_cast<std::ptrdiff_t>(stops.size());
            }
            Analyzer::Terminate worst() const {
                Analyzer::Terminate result = Analyzer::Terminate::None;
                for (Analyzer::Terminate t : stops) {
                    if (rank(t) > rank(result))
                        result = t;
                }
                return result;
            }
            // A path stopped without walking the rest of the range
            bool unwalked() const {
                const Analyzer::Terminate t = worst();
                return t != Analyzer::Terminate::None && t != Analyzer::Terminate::Modified;
            }
            static int rank(Analyzer::Terminate t) {
                switch (t) {
                case Analyzer::Terminate::None:
                case Analyzer::Terminate::Escape:
                    return 0;
                case Analyzer::Terminate::Modified:
                    return 1;
                case Analyzer::Terminate::Conditional:
                    return 2;
                case Analyzer::Terminate::Inconclusive:
                    return 3;
                case Analyzer::Terminate::Bail:
                    return 4;
                }
                cppcheck::unreachable();
            }
        };

        // One way through a statement that forks, e.g. the then block of an if
        struct Branch {
            explicit Branch(Token* tok = nullptr) : endBlock(tok) {}
            // nullptr if there is nothing to walk, e.g. an if without else
            Token* endBlock = nullptr;
            // The condition that holds on the way in. nullptr for the rest of a fork, where no
            // condition of its alternatives holds.
            const Token* condTok = nullptr;
            Analyzer::Action action = Analyzer::Action::None;
            bool escape = false;
            bool escapeUnknown = false;
            bool reachesEnd = true;
            // The condition is false at the end of the block on every path (e.g. 'if (x > 5) x = 5;')
            bool falseAtEnd = false;
            // The paths at the end of the block
            std::vector<Path> paths;
            bool isEscape() const {
                return escape || escapeUnknown;
            }
            bool isConclusiveEscape() const {
                return escape && !escapeUnknown;
            }
            bool isModified() const {
                return action.isModified() && !isConclusiveEscape();
            }
            bool isInconclusive() const {
                return action.isInconclusive() && !isConclusiveEscape();
            }
            bool isDead() const {
                return action.isModified() || action.isInconclusive() || isEscape();
            }
            bool hasGoto() const {
                return endBlock ? ForwardTraversal::hasGoto(endBlock) : false;
            }
        };

        // A statement where the paths part, e.g. an if whose condition is undecided. Each alternative
        // is walked with walkAlternative(), what is left of the incoming path with walkRest(), and
        // joinFork() lets the paths go on.
        struct ForkPoint {
            // The paths of the alternatives go on past the statement. Otherwise they stop at the end
            // of their block and the rest stands for every alternative.
            bool split = false;
            bool conditional = false;
            int branchCount = 0;
        };

        // The paths of the range being walked, apart from the one in the traversal
        struct Range {
            // Whether the paths may part for good at a fork. They may not if the traversal goes on
            // after the range: then one path has to stand for all of them at its end.
            bool canSplit = false;
            // Paths that go on from a token, last one first
            std::vector<std::pair<Path, Token*>> waiting;
            // Paths at the end of the range
            std::vector<Path> reached;
            Outcome outcome;
        };
        Range range;

        bool stopUpdates() {
            analyzeOnly = true;
            return actions.isModified();
        }

        bool stopOnCondition(const Token* condTok) const
        {
            if (analyzer->isConditional() && findAstNode(condTok, [](const Token* tok) {
                return tok->isIncompleteVar();
            }))
                return true;
            return analyzer->stopOnCondition(condTok);
        }

        std::pair<bool, bool> evalCond(const Token* tok, const Token* ctx = nullptr) const {
            return evalCond(*analyzer, tok, ctx);
        }

        static std::pair<bool, bool> evalCond(const Analyzer& a, const Token* tok, const Token* ctx) {
            if (!tok)
                return std::make_pair(false, false);
            std::vector<MathLib::bigint> result = a.evaluate(tok, ctx);
            // TODO: We should convert to bool
            const bool checkThen = std::any_of(result.cbegin(), result.cend(), [](MathLib::bigint x) {
                return x != 0;
            });
            const bool checkElse = std::any_of(result.cbegin(), result.cend(), [](MathLib::bigint x) {
                return x == 0;
            });
            return std::make_pair(checkThen, checkElse);
        }

        bool isConditionTrue(const Token* tok, const Token* ctx = nullptr) const {
            return evalCond(tok, ctx).first;
        }

        template<class T, class F, REQUIRES("T must be a Token class", std::is_convertible<T*, const Token*> )>
        Progress traverseTok(T* tok, const F &f, bool traverseUnknown, T** out = nullptr) {
            if (Token::Match(tok, "asm|goto"))
                return Break(Analyzer::Terminate::Bail);
            if (Token::Match(tok, "setjmp|longjmp (")) {
                // Traverse the parameters of the function before escaping
                traverseRecursive(tok->next()->astOperand2(), f, traverseUnknown);
                return Break(Analyzer::Terminate::Bail);
            }
            if (Token::simpleMatch(tok, "continue")) {
                if (loopEnds.empty())
                    return Break(Analyzer::Terminate::Escape);
                // If we are in a loop then jump to the end
                if (out)
                    *out = loopEnds.back();
            } else if (isEscapeKeyword(tok, settings)) {
                traverseRecursive(tok->astOperand2(), f, traverseUnknown);
                traverseRecursive(tok->astOperand1(), f, traverseUnknown);
                return Break(Analyzer::Terminate::Escape);
            } else if (Token::Match(tok, "%name% (") && isEscapeFunction(tok, settings().library)) {
                // Traverse the parameters of the function before escaping
                traverseRecursive(tok->next()->astOperand2(), f, traverseUnknown);
                return Break(Analyzer::Terminate::Escape);
            } else if (isUnevaluated(tok->previous())) {
                if (out)
                    *out = tok->link();
                return Progress::Skip;
            } else if (tok->astOperand1() && tok->astOperand2() && Token::Match(tok, "?|&&|%oror%")) {
                if (traverseConditional(tok, f, traverseUnknown) == Progress::Break)
                    return Break();
                if (out)
                    *out = nextAfterAstRightmostLeaf(tok);
                return Progress::Skip;
                // Skip lambdas
            } else if (T* lambdaEndToken = findLambdaEndToken(tok)) {
                if (checkScope(lambdaEndToken).isModified())
                    return Break(Analyzer::Terminate::Bail);
                if (out)
                    *out = lambdaEndToken->next();
                // Skip class scope
            } else if (tok->str() == "{" && tok->scope() && tok->scope()->isClassOrStruct()) {
                if (out)
                    *out = tok->link();
            } else {
                if (f(tok) == Progress::Break)
                    return Break();
            }
            return Progress::Continue;
        }

        template<class T, class F, REQUIRES("T must be a Token class", std::is_convertible<T*, const Token*> )>
        Progress traverseRecursive(T* tok, const F &f, bool traverseUnknown, unsigned int recursion=0) {
            if (!tok)
                return Progress::Continue;
            if (recursion > 10000)
                return Progress::Skip;
            T* firstOp = tok->astOperand1();
            T* secondOp = tok->astOperand2();
            // Evaluate:
            //     1. RHS of assignment before LHS
            //     2. Unary op before operand
            //     3. Function arguments before function call
            if (tok->isAssignmentOp() || !secondOp || isFunctionCall(tok))
                std::swap(firstOp, secondOp);
            if (firstOp && traverseRecursive(firstOp, f, traverseUnknown, recursion+1) == Progress::Break)
                return Break();
            const Progress p = tok->isAssignmentOp() ? Progress::Continue : traverseTok(tok, f, traverseUnknown);
            if (p == Progress::Break)
                return Break();
            if (p == Progress::Continue && secondOp && traverseRecursive(secondOp, f, traverseUnknown, recursion+1) == Progress::Break)
                return Break();
            if (tok->isAssignmentOp() && traverseTok(tok, f, traverseUnknown) == Progress::Break)
                return Break();
            return Progress::Continue;
        }

        template<class T, class F, REQUIRES("T must be a Token class", std::is_convertible<T*, const Token*> )>
        Progress traverseConditional(T* tok, F f, bool traverseUnknown) {
            Analyzer::Action action = analyzer->analyze(tok, Analyzer::Direction::Forward);
            if (action.isNone() && Token::Match(tok, "?|&&|%oror%") && tok->astOperand1() && tok->astOperand2()) {
                const T* condTok = tok->astOperand1();
                T* childTok = tok->astOperand2();
                bool checkThen, checkElse;
                std::tie(checkThen, checkElse) = evalCond(condTok);
                if (!checkThen && !checkElse) {
                    if (!traverseUnknown && stopOnCondition(condTok) && tok->str() != "?" && stopUpdates()) {
                        return Progress::Continue;
                    }
                    checkThen = true;
                    checkElse = true;
                }
                if (childTok->str() == ":") {
                    if (checkThen && traverseRecursive(childTok->astOperand1(), f, traverseUnknown) == Progress::Break)
                        return Break();
                    if (checkElse && traverseRecursive(childTok->astOperand2(), f, traverseUnknown) == Progress::Break)
                        return Break();
                } else {
                    if (!checkThen && tok->str() == "&&")
                        return Progress::Continue;
                    if (!checkElse && tok->str() == "||")
                        return Progress::Continue;
                    if (traverseRecursive(childTok, f, traverseUnknown) == Progress::Break)
                        return Break();
                }
            } else {
                return f(tok, action);
            }
            return Progress::Continue;
        }

        Progress update(Token* tok) {
            Analyzer::Action action = analyzer->analyze(tok, Analyzer::Direction::Forward);
            return update(tok, action);
        }

        Progress update(Token* tok, Analyzer::Action action)
        {
            actions |= action;
            if (!action.isNone() && !analyzeOnly)
                analyzer->update(tok, action, Analyzer::Direction::Forward);
            if (action.isInconclusive() && !analyzer->lowerToInconclusive())
                return Break(Analyzer::Terminate::Inconclusive);
            if (action.isInvalid())
                return Break(Analyzer::Terminate::Modified);
            if (action.isWrite() && !action.isRead())
                // Analysis of this write will continue separately
                return Break(Analyzer::Terminate::Modified);
            return Progress::Continue;
        }

        struct AsUpdate {
            ForwardTraversal* self = nullptr;

            explicit AsUpdate(ForwardTraversal* self) : self(self) {}

            template<class... Ts>
            Progress operator()(Ts... xs) const
            {
                assert(self);
                return self->update(xs ...);
            }
        };

        Progress updateTok(Token* tok, Token** out = nullptr) {
            return traverseTok(tok, AsUpdate{this}, false, out);
        }

        Progress updateRecursive(Token* tok) {
            return traverseRecursive(tok, AsUpdate{this}, false);
        }

        struct AsAnalyze {
            ForwardTraversal* self = nullptr;
            Analyzer::Action* result = nullptr;

            AsAnalyze(ForwardTraversal* self, Analyzer::Action* result) : self(self), result(result) {}

            Progress operator()(const Token* tok) const
            {
                assert(self);
                assert(result);
                return (*this)(tok, self->analyzer->analyze(tok, Analyzer::Direction::Forward));
            }

            Progress operator()(const Token* /*unused*/, Analyzer::Action action) const
            {
                assert(self);
                assert(result);
                *result = action;
                if (result->isModified() || result->isInconclusive())
                    return self->Break();
                return Progress::Continue;
            }
        };

        Analyzer::Action analyzeRecursive(const Token* start) {
            Analyzer::Action result = Analyzer::Action::None;
            traverseRecursive(start, AsAnalyze{this, &result}, true);
            return result;
        }

        Analyzer::Action analyzeRange(const Token* start, const Token* end) const {
            return analyzeRange(*analyzer, start, end);
        }

        static Analyzer::Action analyzeRange(const Analyzer& a, const Token* start, const Token* end) {
            Analyzer::Action result = Analyzer::Action::None;
            for (const Token* tok = start; tok && tok != end; tok = tok->next()) {
                Analyzer::Action action = a.analyze(tok, Analyzer::Direction::Forward);
                if (action.isModified() || action.isInconclusive())
                    return action;
                result |= action;
            }
            return result;
        }

        ForwardTraversal fork(bool analyze = false) const {
            ForwardTraversal ft{analyzer, tokenList, errorLogger, settings};
            ft.path() = *this;
            ft.loopEnds = loopEnds;
            ft.forkBudget = forkBudget;
            if (analyze) {
                ft.analyzeOnly = true;
                ft.analyzeTerminate = true;
            }
            ft.actions = Analyzer::Action::None;
            return ft;
        }

        // Another condition-fork may continue past its if: forkDepth bounds nesting, forkBudget the
        // total. <0 = off.
        bool canFork() const {
            assert(forkBudget != nullptr);
            const int depthLimit = settings().vfOptions.maxForwardConditionForkDepth;
            const int budgetLimit = settings().vfOptions.maxForwardConditionForks;
            return (depthLimit < 0 || forkDepth < depthLimit) && (budgetLimit < 0 || *forkBudget < budgetLimit);
        }

        // A value changed in either branch is only possible past the if, on both paths. False if
        // it cannot be lowered.
        static bool lowerAfterBranches(Analyzer& a, const std::vector<const Branch*>& branches) {
            if (std::any_of(branches.cbegin(), branches.cend(), std::mem_fn(&Branch::isModified)) && !a.lowerToPossible())
                return false;
            if (std::any_of(branches.cbegin(), branches.cend(), std::mem_fn(&Branch::isInconclusive)) && !a.lowerToInconclusive())
                return false;
            return true;
        }

        std::vector<ForwardTraversal> tryForkScope(Token* endBlock, bool isModified = false) const {
            if (analyzer->updateScope(endBlock, isModified)) {
                ForwardTraversal ft = fork();
                return {std::move(ft)};
            }
            return std::vector<ForwardTraversal> {};
        }

        std::vector<ForwardTraversal> tryForkUpdateScope(Token* endBlock, bool isModified = false) const {
            std::vector<ForwardTraversal> result = tryForkScope(endBlock, isModified);
            for (ForwardTraversal& ft : result)
                ft.updateAllScopePaths(endBlock);
            return result;
        }

        static bool hasGoto(const Token* endBlock) {
            return Token::findsimplematch(endBlock->link(), "goto", endBlock);
        }

        static bool hasJump(const Token* endBlock) {
            return Token::findmatch(endBlock->link(), "goto|break", endBlock);
        }

        bool isEscapeScope(const Token* endBlock, bool& unknown) const {
            const Token* ftok = nullptr;
            const bool r = isReturnScope(endBlock, settings().library, &ftok);
            if (!r && ftok)
                unknown = true;
            return r;
        }

        Analyzer::Action analyzeScope(const Token* endBlock) const {
            return analyzeRange(endBlock->link(), endBlock);
        }

        Analyzer::Action checkScope(Token* endBlock) const {
            Analyzer::Action a = analyzeScope(endBlock);
            tryForkUpdateScope(endBlock, a.isModified());
            return a;
        }

        Analyzer::Action checkScope(const Token* endBlock) const {
            Analyzer::Action a = analyzeScope(endBlock);
            return a;
        }

        // Walk a block on the path in the traversal. The paths do not part for good inside it: each
        // one would have to be followed past the block to the end of the range, which costs too much.
        // A path that stops in the block has stopped in the range; covered: another path goes on for
        // it past the block.
        Branch walkBranch(Token* endBlock, int depth, bool covered)
        {
            const Analyzer::Action outerActions = actions;
            actions = Analyzer::Action::None;
            Range block = walkPaths(endBlock->link(), endBlock, depth, false);
            range.outcome.add(block.outcome, covered);
            // The path walked last is no longer in the traversal if it is at the end of the block
            Branch branch = resolve(endBlock, block.outcome, analyzer ? *analyzer : *block.reached.back().analyzer);
            branch.paths = std::move(block.reached);
            for (Path& p : branch.paths)
                p.actions |= outerActions;
            return branch;
        }

        Branch resolve(Token* endBlock, const Outcome& paths, const Analyzer& a) const
        {
            Branch branch{endBlock};
            branch.action = paths.action;
            branch.reachesEnd = paths.reached > 0;
            if (paths.allEscape()) {
                branch.escape = true;
                // The paths can miss a way through the block: a call is taken to return what an
                // earlier call of the same function returned. Unless the block structurally always
                // escapes, it may fall through and change the value on the way.
                bool structuralUnknown = false;
                const bool structuralEscape = isEscapeScope(endBlock, structuralUnknown);
                branch.escapeUnknown = !structuralEscape || structuralUnknown;
                if (branch.escapeUnknown)
                    branch.action |= analyzeRange(a, endBlock->link(), endBlock);
                return branch;
            }
            // Detect an escape the paths did not flag (e.g. an unknown noreturn call);
            // escapeUnknown reports a possible (unknown) escape.
            branch.escape = isEscapeScope(endBlock, branch.escapeUnknown);
            if (paths.unwalked())
                branch.action |= analyzeRange(a, endBlock->link(), endBlock);
            return branch;
        }

        // The path in the traversal stops before the end of the range
        void stopPath(Analyzer::Terminate t = Analyzer::Terminate::None)
        {
            Break(t);
            range.outcome.stop(actions, terminate);
        }

        // The paths go on after tok, the first one first
        Progress resume(std::vector<Path> paths, Token* tok)
        {
            for (auto it = paths.rbegin(); it != paths.rend(); ++it)
                range.waiting.emplace_back(std::move(*it), tok->next());
            return Progress::Forked;
        }

        // Walk the block that the evaluated condition takes
        Progress updateTakenBranch(Token* endBlock, const Token* skippedBlock, const Token* condTok, Token* ifEnd, int depth)
        {
            // The condition is only "known" because of an earlier assumption, so the
            // skipped block could still modify the value -> lower to possible
            if (!condTok->hasKnownIntValue() && skippedBlock && analyzeScope(skippedBlock).isModified() &&
                !analyzer->lowerToPossible())
                return Break(Analyzer::Terminate::Bail);
            if (!endBlock) {
                // Record the state past the skipped block, so that the conditions evaluated later do
                // not each look for changes in it
                if (ifEnd->next())
                    analyzer->updateState(ifEnd->next());
                return Progress::Continue;
            }
            updateScopeState(endBlock);
            Branch branch = walkBranch(endBlock, depth - 1, false);
            std::vector<Path> paths;
            for (Path& p : branch.paths) {
                path() = std::move(p);
                // The branch was entered because of the tracked value; if it might not
                // return (it ends in a call to an unknown, possibly noreturn function)
                // then the value might not flow past the branch.
                if (!condTok->hasKnownIntValue() && !branch.escape && branch.escapeUnknown && !analyzer->lowerToInconclusive())
                    stopPath(Analyzer::Terminate::Bail);
                else
                    paths.push_back(std::move(path()));
            }
            return resume(std::move(paths), ifEnd);
        }

        // The paths part at the path in the traversal
        ForkPoint startFork(const Token* condTok) const
        {
            ForkPoint point;
            point.split = range.canSplit && canFork();
            point.conditional = stopOnCondition(condTok);
            point.branchCount = branchCount;
            return point;
        }

        // Walk a block on a copy of the incoming path, where condTok holds
        Branch walkAlternative(const ForkPoint& point, const Path& incoming, const Token* condTok, Token* endBlock, int depth)
        {
            path() = incoming;
            // The value only flows into the block when the condition can split it; for an opaque or
            // correlated condition (e.g. 'if (f(x))') it does not, so the path is analyze-only: the
            // block's effect is still tracked but nothing is reported in it.
            if (!analyzer->updateScope(endBlock, false)) {
                analyzeOnly = true;
                analyzeTerminate = true;
            }
            if (point.split) {
                ++(*forkBudget);
                ++forkDepth;
            }
            analyzer->assume(condTok, true, Analyzer::Assume::Pending);
            Branch branch = walkBranch(endBlock, depth, !point.split);
            branch.condTok = condTok;
            branch.falseAtEnd = !point.split && std::all_of(branch.paths.cbegin(), branch.paths.cend(), [&](const Path& p) {
                const std::pair<bool, bool> check = evalCond(*p.analyzer, condTok, endBlock->previous());
                return !check.first && check.second;
            });
            return branch;
        }

        // Walk the incoming path where no condition of the alternatives holds. endBlock is the block
        // for that, if any. The path goes on after forkEnd.
        Branch walkRest(const ForkPoint& point,
                        Path incoming,
                        const std::vector<Branch>& alternatives,
                        Token* endBlock,
                        const Token* forkEnd,
                        int depth)
        {
            path() = std::move(incoming);
            const unsigned int pending = endBlock ? Analyzer::Assume::Pending : Analyzer::Assume::None;
            bool assumed = false;
            for (const Branch& alt : alternatives) {
                actions |= alt.action;
                // The condition is an assumption on this path if the alternative drops the value. If
                // its paths go on past the fork the value is the same with and without it. Otherwise
                // this path stands for the alternative as well and records that the condition is
                // false only if that holds on both. With a block the state is recorded after it.
                if (alt.isDead())
                    analyzer->assume(alt.condTok, false, Analyzer::Assume::None | pending);
                else if (alt.reachesEnd && (point.split || alt.falseAtEnd))
                    analyzer->assume(alt.condTok, false, Analyzer::Assume::Quiet | Analyzer::Assume::Absolute | pending);
                else
                    continue;
                assumed = true;
            }
            // An assumption records the state where the path goes on. Without one the state stays
            // at an earlier token, and every condition evaluated later looks for changes from there.
            if (!endBlock) {
                if (!assumed && forkEnd->next())
                    analyzer->updateState(forkEnd->next());
                Branch rest;
                rest.paths.push_back(std::move(path()));
                return rest;
            }
            if (!assumed)
                updateScopeState(endBlock);
            Branch rest = walkBranch(endBlock, depth, false);
            for (Path& p : rest.paths)
                p.analyzer->updateState(endBlock->previous());
            return rest;
        }

        // Let the paths at the end of the branches go on after tok
        Progress joinFork(const ForkPoint& point, std::vector<Branch> alternatives, Branch rest, Token* tok)
        {
            std::vector<const Branch*> branches{&rest};
            std::transform(alternatives.cbegin(), alternatives.cend(), std::back_inserter(branches), [](const Branch& alt) {
                return &alt;
            });
            const Analyzer::Action action =
                std::accumulate(branches.cbegin(), branches.cend(), Analyzer::Action{Analyzer::Action::None}, [](Analyzer::Action a, const Branch* branch) {
                return a | branch->action;
            });
            const bool dead = std::any_of(branches.cbegin(), branches.cend(), std::mem_fn(&Branch::isDead));
            const bool jumps = std::any_of(branches.cbegin(), branches.cend(), std::mem_fn(&Branch::hasGoto));
            std::vector<Path> paths;
            for (Branch& alt : alternatives) {
                for (Path& p : alt.paths) {
                    path() = std::move(p);
                    actions |= action;
                    if (jumps) {
                        stopPath(Analyzer::Terminate::Bail);
                    } else if (alt.isEscape()) {
                        stopPath(Analyzer::Terminate::Escape);
                    } else if (!point.split) {
                        // The rest goes on for this path. If the rest stopped, nothing does.
                        if (!rest.reachesEnd)
                            stopPath();
                    } else if (!lowerAfterBranches(*analyzer, branches)) {
                        stopPath();
                    } else {
                        // The branch limit counts the branches on the way past the fork, as it does
                        // for the rest
                        branchCount = point.branchCount;
                        // Anchor the state (and the block's assignments) at the block end
                        analyzer->assume(alt.condTok, true, Analyzer::Assume::Quiet | Analyzer::Assume::Absolute);
                        paths.push_back(std::move(path()));
                    }
                }
            }
            for (Path& p : rest.paths) {
                path() = std::move(p);
                actions |= action;
                if (dead && point.conditional && stopUpdates())
                    stopPath(Analyzer::Terminate::Conditional);
                else if (!lowerAfterBranches(*analyzer, branches))
                    stopPath(Analyzer::Terminate::Bail);
                else if (jumps)
                    stopPath(Analyzer::Terminate::Bail);
                else
                    paths.push_back(std::move(path()));
            }
            return resume(std::move(paths), tok);
        }

        // Neither outcome of the condition is known: walk each on its own paths
        Progress forkIf(const Token* condTok, Token* thenEnd, Token* elseEnd, int depth)
        {
            const ForkPoint point = startFork(condTok);
            Token* ifEnd = elseEnd ? elseEnd : thenEnd;
            Path incoming = std::move(path());
            std::vector<Branch> alternatives;
            alternatives.push_back(walkAlternative(point, incoming, condTok, thenEnd, depth - 1));
            Branch rest = walkRest(point, std::move(incoming), alternatives, elseEnd, ifEnd, depth - 1);
            return joinFork(point, std::move(alternatives), std::move(rest), ifEnd);
        }

        bool reentersLoop(Token* endBlock, const Token* condTok, const Token* stepTok) const {
            if (!condTok)
                return true;
            if (Token::simpleMatch(condTok, ":"))
                return true;
            bool stepChangesCond = false;
            if (stepTok) {
                std::pair<const Token*, const Token*> exprToks = stepTok->findExpressionStartEndTokens();
                if (exprToks.first != nullptr && exprToks.second != nullptr)
                    stepChangesCond |=
                        findExpressionChanged(condTok, exprToks.first, exprToks.second->next(), settings) != nullptr;
            }
            const bool bodyChangesCond = findExpressionChanged(condTok, endBlock->link(), endBlock, settings);
            // Check for mutation in the condition
            const bool condChanged =
                nullptr != findAstNode(condTok, [&](const Token* tok) {
                return isVariableChanged(tok, 0, settings);
            });
            const bool changed = stepChangesCond || bodyChangesCond || condChanged;
            if (!changed)
                return true;
            ForwardTraversal ft = fork(true);
            ft.updateScope(endBlock);
            return ft.isConditionTrue(condTok) && bodyChangesCond;
        }

        Progress updateInnerLoop(Token* endBlock, Token* stepTok, Token* condTok) {
            loopEnds.push_back(endBlock);
            OnExit oe{[&] {
                    loopEnds.pop_back();
                }};
            if (endBlock && updateScope(endBlock) == Progress::Break)
                return Break();
            if (stepTok && updateRecursive(stepTok) == Progress::Break)
                return Break();
            if (condTok && !Token::simpleMatch(condTok, ":") && updateRecursive(condTok) == Progress::Break)
                return Break();
            return Progress::Continue;
        }

        Progress updateLoop(const Token* endToken,
                            Token* endBlock,
                            Token* condTok,
                            Token* initTok = nullptr,
                            Token* stepTok = nullptr,
                            bool exit = false) {
            if (initTok && updateRecursive(initTok) == Progress::Break)
                return Break();
            const bool isDoWhile = precedes(endBlock, condTok);
            bool checkThen = true;
            bool checkElse = false;
            if (condTok && !Token::simpleMatch(condTok, ":"))
                std::tie(checkThen, checkElse) = evalCond(condTok, isDoWhile ? endBlock->previous() : nullptr);
            // exiting a do while(false)
            if (checkElse && exit) {
                if (hasJump(endBlock)) {
                    if (!analyzer->lowerToPossible())
                        return Break(Analyzer::Terminate::Bail);
                    if (analyzer->isConditional() && stopUpdates())
                        return Break(Analyzer::Terminate::Conditional);
                }
                return Progress::Continue;
            }
            Analyzer::Action bodyAnalysis = analyzeScope(endBlock);
            Analyzer::Action allAnalysis = bodyAnalysis;
            Analyzer::Action condAnalysis;
            if (condTok) {
                condAnalysis = analyzeRecursive(condTok);
                allAnalysis |= condAnalysis;
            }
            if (stepTok)
                allAnalysis |= analyzeRecursive(stepTok);
            actions |= allAnalysis;
            // do while(false) is not really a loop
            if (checkElse && isDoWhile &&
                (condTok->hasKnownIntValue() ||
                 (!bodyAnalysis.isModified() && !condAnalysis.isModified() && condAnalysis.isRead()))) {
                if (updateScope(endBlock) == Progress::Break)
                    return Break();
                return updateRecursive(condTok);
            }
            if (allAnalysis.isInconclusive()) {
                if (!analyzer->lowerToInconclusive())
                    return Break(Analyzer::Terminate::Bail);
            } else if (allAnalysis.isModified() || (exit && allAnalysis.isIdempotent())) {
                if (!analyzer->lowerToPossible())
                    return Break(Analyzer::Terminate::Bail);
            }

            if (condTok && !Token::simpleMatch(condTok, ":")) {
                if (!isDoWhile || (!bodyAnalysis.isModified() && !bodyAnalysis.isIdempotent()))
                    if (updateRecursive(condTok) == Progress::Break)
                        return Break();
            }
            if (!checkThen && !checkElse && !isDoWhile && stopOnCondition(condTok) && stopUpdates())
                return Break(Analyzer::Terminate::Conditional);
            // condition is false, we don't enter the loop
            if (checkElse && !isDoWhile)
                return Progress::Continue;
            if (checkThen || isDoWhile) {
                // Since we are re-entering the loop then assume the condition is true to update the state
                if (exit)
                    analyzer->assume(condTok, true, Analyzer::Assume::Quiet | Analyzer::Assume::Absolute);
                if (updateInnerLoop(endBlock, stepTok, condTok) == Progress::Break)
                    return Break();
                // If loop re-enters then it could be modified again
                if (allAnalysis.isModified() && reentersLoop(endBlock, condTok, stepTok))
                    return Break(Analyzer::Terminate::Bail);
                if (allAnalysis.isIncremental())
                    return Break(Analyzer::Terminate::Bail);
            } else if (allAnalysis.isModified()) {
                std::vector<ForwardTraversal> ftv = tryForkScope(endBlock, allAnalysis.isModified());
                bool forkContinue = true;
                for (ForwardTraversal& ft : ftv) {
                    if (condTok)
                        ft.analyzer->assume(condTok, false, Analyzer::Assume::Quiet);
                    if (ft.updateInnerLoop(endBlock, stepTok, condTok) == Progress::Break)
                        forkContinue = false;
                }

                // TODO: Don't bail on missing condition
                if (!condTok)
                    return Break(Analyzer::Terminate::Bail);
                if (analyzer->isConditional() && stopUpdates())
                    return Break(Analyzer::Terminate::Conditional);
                analyzer->assume(condTok, false);
                if (forkContinue) {
                    for (ForwardTraversal& ft : ftv) {
                        if (!ft.actions.isIncremental())
                            ft.updateAllPaths(endBlock, endToken);
                    }
                }
                if (allAnalysis.isIncremental())
                    return Break(Analyzer::Terminate::Bail);
            } else {
                if (updateInnerLoop(endBlock, stepTok, condTok) == Progress::Break)
                    return Progress::Break;
                if (allAnalysis.isIncremental())
                    return Break(Analyzer::Terminate::Bail);
            }
            return Progress::Continue;
        }

        Progress updateLoopExit(const Token* endToken,
                                Token* endBlock,
                                Token* condTok,
                                Token* initTok = nullptr,
                                Token* stepTok = nullptr) {
            return updateLoop(endToken, endBlock, condTok, initTok, stepTok, true);
        }

        void updateScopeState(const Token* endBlock)
        {
            assert(endBlock->link());
            const Token* ctx = endBlock->link()->previous();
            if (Token::simpleMatch(ctx, ")"))
                ctx = ctx->link()->previous();
            if (ctx)
                analyzer->updateState(ctx);
        }

        Progress updateScope(Token* endBlock, int depth = 20)
        {
            if (!endBlock)
                return Break();
            updateScopeState(endBlock);
            return updateRange(endBlock->link(), endBlock, depth);
        }

        Progress updateAllScopePaths(Token* endBlock, int depth = 20)
        {
            if (!endBlock)
                return Break();
            updateScopeState(endBlock);
            return updateAllPaths(endBlock->link(), endBlock, depth);
        }

        // This traversal goes on after the range, so the paths do not part for good in it: at a fork
        // one path stands for every alternative.
        Progress updateRange(Token* start, const Token* end, int depth = 20) {
            Range walked = walkPaths(start, end, depth, false);
            setResult(walked.outcome, end);
            if (walked.reached.empty())
                return Progress::Break;
            path() = std::move(walked.reached.front());
            return Progress::Continue;
        }

        // Follow every path to the end of the range. This traversal gets their joint result and must
        // not go on after the range.
        Progress updateAllPaths(Token* start, const Token* end, int depth = 20) {
            const Range walked = walkPaths(start, end, depth, true);
            setResult(walked.outcome, end);
            return walked.reached.empty() ? Progress::Break : Progress::Continue;
        }

        void setResult(const Outcome& outcome, const Token* end) {
            // A path that stopped without an escape was not followed to one, but the code can show
            // that there is no way to the end of the range
            const bool escapes = outcome.allEscape() ||
                                 (outcome.reached == 0 && outcome.hasEscape() && isReturnScope(end, settings().library));
            actions = outcome.action;
            terminate = escapes ? Analyzer::Terminate::Escape : outcome.worst();
        }

        // Walk the path in the traversal and the paths that fork off it from start to end. No path is
        // left in the traversal: the ones that go on are in the result.
        Range walkPaths(Token* start, const Token* end, int depth, bool split) {
            Range outer = std::move(range);
            range = Range{};
            range.canSplit = split;
            Token* tok = start;
            for (;;) {
                const Progress p = walkRange(tok, end, depth);
                if (p == Progress::Continue) {
                    range.outcome.reach(actions);
                    range.reached.push_back(std::move(path()));
                } else if (p == Progress::Break) {
                    range.outcome.stop(actions, terminate);
                }
                if (range.waiting.empty())
                    break;
                path() = std::move(range.waiting.back().first);
                tok = range.waiting.back().second;
                range.waiting.pop_back();
            }
            Range walked = std::move(range);
            range = std::move(outer);
            return walked;
        }

        /**
         * Walk the path in the traversal until it stops, reaches the end of the range or forks
         * @throws InternalError thrown on cyclic analysis
         */
        Progress walkRange(Token* start, const Token* end, int depth) {
            if (depth < 0)
                return Break(Analyzer::Terminate::Bail);
            std::size_t i = 0;
            for (Token* tok = start; precedes(tok, end); tok = tok->next()) {
                Token* next = nullptr;
                if (tok->index() <= i)
                    throw InternalError(tok, "Cyclic forward analysis.");
                i = tok->index();

                if (tok->link()) {
                    // Skip casts..
                    if (tok->str() == "(" && !tok->astOperand2() && tok->isCast()) {
                        tok = tok->link();
                        continue;
                    }
                    // Skip template arguments..
                    if (tok->str() == "<") {
                        tok = tok->link();
                        continue;
                    }
                }

                // Evaluate RHS of assignment before LHS
                if (Token* assignTok = assignExpr(tok)) {
                    if (updateRecursive(assignTok) == Progress::Break)
                        return Break();
                    tok = nextAfterAstRightmostLeaf(assignTok);
                    if (!tok)
                        return Break();
                } else if (Token::simpleMatch(tok, ") {") && Token::Match(tok->link()->previous(), "for|while (") &&
                           !Token::simpleMatch(tok->link()->astOperand2(), ":")) {
                    // In the middle of a loop structure so bail
                    return Break(Analyzer::Terminate::Bail);
                } else if (tok->str() == ";" && tok->astParent()) {
                    Token* top = tok->astTop();
                    if (Token::Match(top->previous(), "for|while (") && Token::simpleMatch(top->link(), ") {")) {
                        Token* endCond = top->link();
                        Token* endBlock = endCond->linkAt(1);
                        Token* condTok = getCondTok(top);
                        Token* stepTok = getStepTok(top);
                        // The semicolon should belong to the initTok otherwise something went wrong, so just bail
                        if (tok->astOperand2() != condTok && !Token::simpleMatch(tok->astOperand2(), ";"))
                            return Break(Analyzer::Terminate::Bail);
                        if (updateLoop(end, endBlock, condTok, nullptr, stepTok) == Progress::Break)
                            return Break();
                    }
                } else if (tok->str() == "break") {
                    const Token *scopeEndToken = findNextTokenFromBreak(tok);
                    if (!scopeEndToken)
                        return Break();
                    tok = skipTo(tok, scopeEndToken, end);
                    if (!precedes(tok, end))
                        return Break(Analyzer::Terminate::Escape);
                    if (!analyzer->lowerToPossible())
                        return Break(Analyzer::Terminate::Bail);
                    // TODO: Don't break, instead move to the outer scope
                    if (!tok)
                        return Break();
                } else if (!tok->variable() && (Token::Match(tok, "%name% :") || tok->str() == "case")) {
                    if (!analyzer->lowerToPossible())
                        return Break(Analyzer::Terminate::Bail);
                } else if (tok->link() && tok->str() == "}" && tok == tok->scope()->bodyEnd) { // might be an init list
                    const Scope* scope = tok->scope();
                    if (contains({ScopeType::eDo, ScopeType::eFor, ScopeType::eWhile, ScopeType::eIf, ScopeType::eElse, ScopeType::eSwitch}, scope->type)) {
                        const bool inElse = scope->type == ScopeType::eElse;
                        const bool inDoWhile = scope->type == ScopeType::eDo;
                        const bool inLoop = contains({ScopeType::eDo, ScopeType::eFor, ScopeType::eWhile}, scope->type);
                        const bool hasElse = Token::simpleMatch(tok, "} else {");
                        Token* condTok = getCondTokFromEnd(tok);
                        if (!condTok)
                            return Break();
                        // When the 'else' branch escapes (e.g. returns), control can only continue
                        // here via the 'then' branch, so the value established there is still
                        // definite - keep it known instead of lowering to possible.
                        bool elseEscape = false;
                        if (!inLoop && !inElse && hasElse) {
                            bool unknownEscape = false;
                            elseEscape = isEscapeScope(tok->linkAt(2), unknownEscape);
                        }
                        if (!condTok->hasKnownIntValue() || inLoop) {
                            if (!elseEscape && !analyzer->lowerToPossible())
                                return Break(Analyzer::Terminate::Bail);
                        } else if (condTok->getKnownIntValue() == inElse) {
                            return Break();
                        }
                        // Handle loop
                        if (inLoop) {
                            Token* stepTok = getStepTokFromEnd(tok);
                            bool checkThen, checkElse;
                            std::tie(checkThen, checkElse) = evalCond(condTok);
                            if (stepTok && !checkElse) {
                                if (updateRecursive(stepTok) == Progress::Break)
                                    return Break();
                                if (updateRecursive(condTok) == Progress::Break)
                                    return Break();
                                // Reevaluate condition
                                std::tie(checkThen, checkElse) = evalCond(condTok);
                            }
                            if (!checkElse) {
                                if (updateLoopExit(end, tok, condTok, nullptr, stepTok) == Progress::Break)
                                    return Break();
                            }
                        }
                        analyzer->assume(condTok, !inElse);
                        assert(!inDoWhile || Token::simpleMatch(tok, "} while ("));
                        if (hasElse || inDoWhile)
                            tok = tok->linkAt(2);
                    } else if (contains({ScopeType::eTry, ScopeType::eCatch}, scope->type)) {
                        if (!analyzer->lowerToPossible())
                            return Break(Analyzer::Terminate::Bail);
                    } else if (scope->type == ScopeType::eLambda) {
                        return Break();
                    }
                } else if (tok->isControlFlowKeyword() && Token::Match(tok, "if|while|for (") &&
                           Token::simpleMatch(tok->linkAt(1), ") {")) {
                    if ((settings().vfOptions.maxForwardBranches > 0) && (++branchCount > settings().vfOptions.maxForwardBranches)) {
                        // TODO: should be logged on function-level instead of file-level
                        if (settings().severity.isEnabled(Severity::information)) {
                            reportError(Severity::information, "normalCheckLevelMaxBranches", "Limiting analysis of branches. Use --check-level=exhaustive to analyze all branches.");
                        }
                        return Break(Analyzer::Terminate::Bail);
                    }
                    Token* endCond = tok->linkAt(1);
                    Token* endBlock = endCond->linkAt(1);
                    Token* condTok = getCondTok(tok);
                    Token* initTok = getInitTok(tok);
                    if (initTok && updateRecursive(initTok) == Progress::Break)
                        return Break();
                    if (Token::Match(tok, "for|while (")) {
                        // For-range loop
                        if (Token::simpleMatch(condTok, ":")) {
                            Token* conTok = condTok->astOperand2();
                            if (conTok && updateRecursive(conTok) == Progress::Break)
                                return Break();
                            bool isEmpty = false;
                            std::vector<MathLib::bigint> result =
                                analyzer->evaluate(Analyzer::Evaluate::ContainerEmpty, conTok);
                            if (result.empty())
                                analyzer->assume(conTok, false, Analyzer::Assume::ContainerEmpty);
                            else
                                isEmpty = result.front() != 0;
                            if (!isEmpty && updateLoop(end, endBlock, condTok) == Progress::Break)
                                return Break();
                        } else {
                            Token* stepTok = getStepTok(tok);
                            // Dont pass initTok since it was already evaluated
                            if (updateLoop(end, endBlock, condTok, nullptr, stepTok) == Progress::Break)
                                return Break();
                        }
                        tok = endBlock;
                    } else {
                        // Traverse condition
                        if (updateRecursive(condTok) == Progress::Break)
                            return Break();
                        // Check if condition is true or false
                        bool checkThen, checkElse;
                        std::tie(checkThen, checkElse) = evalCond(condTok);
                        if (!checkThen && !checkElse && stopOnCondition(condTok) && stopUpdates())
                            return Break(Analyzer::Terminate::Conditional);
                        Token* elseEnd = Token::simpleMatch(endBlock, "} else {") ? endBlock->linkAt(2) : nullptr;
                        tok = elseEnd ? elseEnd : endBlock;
                        if (!checkThen && !checkElse)
                            return forkIf(condTok, endBlock, elseEnd, depth);
                        const Progress p =
                            updateTakenBranch(checkThen ? endBlock : elseEnd, checkThen ? elseEnd : endBlock, condTok, tok, depth);
                        if (p != Progress::Continue)
                            return p;
                    }
                } else if (Token::simpleMatch(tok, "try {")) {
                    Token* endBlock = tok->linkAt(1);
                    ForwardTraversal tryTraversal = fork();
                    tryTraversal.updateAllScopePaths(endBlock, depth - 1);
                    bool bail = tryTraversal.actions.isModified();
                    if (bail) {
                        actions = tryTraversal.actions;
                        terminate = tryTraversal.terminate;
                        return Break();
                    }

                    while (Token::simpleMatch(endBlock, "} catch (")) {
                        Token* endCatch = endBlock->linkAt(2);
                        if (!Token::simpleMatch(endCatch, ") {"))
                            return Break();
                        endBlock = endCatch->linkAt(1);
                        ForwardTraversal ft = fork();
                        ft.updateAllScopePaths(endBlock, depth - 1);
                        bail |= ft.terminate != Analyzer::Terminate::None || ft.actions.isModified();
                    }
                    if (bail)
                        return Break();
                    tok = endBlock;
                } else if (Token::simpleMatch(tok, "do {")) {
                    Token* endBlock = tok->linkAt(1);
                    Token* condTok = Token::simpleMatch(endBlock, "} while (") ? endBlock->tokAt(2)->astOperand2() : nullptr;
                    if (updateLoop(end, endBlock, condTok) == Progress::Break)
                        return Break();
                    if (condTok)
                        tok = endBlock->linkAt(2)->next();
                    else
                        tok = endBlock;
                } else if (Token::Match(tok, "assert|ASSERT (")) {
                    const Token* condTok = tok->next()->astOperand2();
                    bool checkThen, checkElse;
                    std::tie(checkThen, checkElse) = evalCond(condTok);
                    if (checkElse)
                        return Break();
                    if (!checkThen)
                        analyzer->assume(condTok, true, Analyzer::Assume::Quiet | Analyzer::Assume::Absolute);
                } else if (Token::simpleMatch(tok, "switch (")) {
                    if (updateRecursive(tok->next()->astOperand2()) == Progress::Break)
                        return Break();
                    actions |= Analyzer::Action::Write; // bailout for switch scope
                    return Break();
                } else if (Token* callTok = callExpr(tok)) {
                    // TODO: Dont traverse tokens a second time
                    if (start != callTok && tok != callTok && (tok->str() != "." || tok != callTok->astOperand1()) && updateRecursive(callTok->astOperand1()) == Progress::Break)
                        return Break();
                    // Since the call could be an unknown macro, traverse the tokens as a range instead of recursively
                    if (!Token::simpleMatch(callTok, "( )") &&
                        updateRange(callTok->next(), callTok->link(), depth - 1) == Progress::Break)
                        return Break();
                    if (updateTok(callTok) == Progress::Break)
                        return Break();
                    tok = callTok->link();
                    if (!tok)
                        return Break();
                } else {
                    if (updateTok(tok, &next) == Progress::Break)
                        return Break();
                    if (next) {
                        if (precedes(next, end))
                            tok = next->previous();
                        else
                            return Progress::Continue;
                    }
                }
                // Prevent infinite recursion
                if (tok->next() == start)
                    break;
            }
            return Progress::Continue;
        }

        void reportError(Severity severity, const std::string& id, const std::string& msg) const {
            ErrorMessage::FileLocation loc(tokenList().getSourceFilePath(), 0, 0);
            const ErrorMessage errmsg({std::move(loc)}, tokenList().getSourceFilePath(), severity, msg, id, Certainty::normal);
            errorLogger().reportErr(errmsg);
        }

        static bool isFunctionCall(const Token* tok)
        {
            if (!Token::simpleMatch(tok, "("))
                return false;
            if (tok->isCast())
                return false;
            if (!tok->isBinaryOp())
                return false;
            if (Token::simpleMatch(tok->link(), ") {"))
                return false;
            if (isUnevaluated(tok->previous()))
                return false;
            return Token::Match(tok->previous(), "%name%|)|]|>");
        }

        static Token* assignExpr(Token* tok) {
            while (tok->astParent() && astIsLHS(tok)) {
                if (tok->astParent()->isAssignmentOp())
                    return tok->astParent();
                tok = tok->astParent();
            }
            return nullptr;
        }

        static Token* callExpr(Token* tok)
        {
            while (tok->astParent() && astIsLHS(tok)) {
                if (!Token::Match(tok, "%name%|::|<|."))
                    break;
                if (Token::simpleMatch(tok, "<") && !tok->link())
                    break;
                tok = tok->astParent();
            }
            if (isFunctionCall(tok))
                return tok;
            return nullptr;
        }

        static Token* skipTo(Token* tok, const Token* dest, const Token* end = nullptr) {
            if (end && dest->index() > end->index())
                return nullptr;
            const int i = dest->index() - tok->index();
            if (i > 0)
                return tok->tokAt(dest->index() - tok->index());
            return nullptr;
        }

        static Token* getStepTokFromEnd(Token* tok) {
            if (!Token::simpleMatch(tok, "}"))
                return nullptr;
            Token* end = tok->link()->previous();
            if (!Token::simpleMatch(end, ")"))
                return nullptr;
            return getStepTok(end->link());
        }
    };
}

Analyzer::Result valueFlowGenericForward(Token* start, const Token* end, const ValuePtr<Analyzer>& a, const TokenList& tokenList, ErrorLogger& errorLogger, const Settings& settings)
{
    if (a->invalid())
        return Analyzer::Result{Analyzer::Action::None, Analyzer::Terminate::Bail};
    ForwardTraversal ft{a, tokenList, errorLogger, settings};
    if (start)
        ft.analyzer->updateState(start);
    ft.updateAllPaths(start, end);
    return Analyzer::Result{ft.actions, ft.terminate};
}

Analyzer::Result valueFlowGenericForward(Token* start, const ValuePtr<Analyzer>& a, const TokenList& tokenList, ErrorLogger& errorLogger, const Settings& settings)
{
    if (Settings::terminated())
        throw TerminateException();
    if (a->invalid())
        return Analyzer::Result{Analyzer::Action::None, Analyzer::Terminate::Bail};
    ForwardTraversal ft{a, tokenList, errorLogger, settings};
    (void)ft.updateRecursive(start);
    return Analyzer::Result{ ft.actions, ft.terminate };
}
