#include "reverseanalyzer.h"
#include "forwardanalyzer.h"
#include "analyzer.h"
#include "astutils.h"
#include "settings.h"
#include "symboldatabase.h"
#include "token.h"
#include "valueptr.h"

#include <algorithm>
#include <functional>

struct ReverseTraversal {
    ReverseTraversal(const ValuePtr<GenericAnalyzer>& analyzer, const Settings* settings)
        : analyzer(analyzer), settings(settings)
    {}
    ValuePtr<GenericAnalyzer> analyzer;
    const Settings* settings;

    std::pair<bool, bool> evalCond(const Token* tok) {
        std::vector<int> result = analyzer->evaluate(tok);
        bool checkThen = std::any_of(result.begin(), result.end(), [](int x) {
            return x;
        });
        bool checkElse = std::any_of(result.begin(), result.end(), [](int x) {
            return !x;
        });
        return std::make_pair(checkThen, checkElse);
    }

    bool update(Token* tok) {
        GenericAnalyzer::Action action = analyzer->analyze(tok);
        if (action.isRead())
            analyzer->update(tok, action);
        if (action.isInconclusive() && !analyzer->lowerToInconclusive())
            return false;
        if (action.isModified())
            return false;
        return true;
    }

    GenericAnalyzer::Action analyzeRecursive(const Token* start) {
        GenericAnalyzer::Action result = GenericAnalyzer::Action::None;
        visitAstNodes(start, [&](const Token *tok) {
            result |= analyzer->analyze(tok);
            if (result.isModified() || result.isInconclusive())
                return ChildrenToVisit::done;
            return ChildrenToVisit::op1_and_op2;
        });
        return result;
    }

    GenericAnalyzer::Action analyzeRange(const Token* start, const Token* end) {
        GenericAnalyzer::Action result = GenericAnalyzer::Action::None;
        for (const Token* tok = start; tok && tok != end; tok = tok->next()) {
            GenericAnalyzer::Action action = analyzer->analyze(tok);
            if (action.isModified() || action.isInconclusive())
                return action;
            result |= action;
        }
        return result;
    }

    Token* isDeadCode(Token *tok)
    {
        int opSide = 0;
        for (; tok && tok->astParent(); tok = tok->astParent()) {
            Token *parent = tok->astParent();
            if (tok != parent->astOperand2())
                continue;
            if (Token::Match(parent, ":")) {
                if (astIsLHS(tok))
                    opSide = 1;
                else if (astIsRHS(tok))
                    opSide = 1;
                else
                    opSide = 0;
            }
            if (!Token::Match(parent, "%oror%|&&|?"))
                continue;
            Token* condTok = parent->astOperand1();
            if (!condTok)
                continue;
            bool checkThen, checkElse;
            std::tie(checkThen, checkElse) = evalCond(condTok);

            if (!checkThen && !checkElse) {
                GenericAnalyzer::Action action = analyzeRecursive(condTok);
                if (action.isRead() || action.isModified())
                    return parent;
            }

            if (parent->str() == "?") {
                if (!checkThen && opSide == 1)
                    continue;
                if (!checkElse && opSide == 2)
                    continue;
            }
            if (!checkThen && parent->str() == "&&")
                continue;
            if (!checkElse && parent->str() == "||")
                continue;
            return parent;
        }
        return nullptr;
    }

    void traverse(Token* start) {
        for (Token *tok = start->previous(); tok; tok = tok->previous()) {
            if (tok == start || (tok->str() == "{" && (tok->scope()->type == Scope::ScopeType::eFunction || tok->scope()->type == Scope::ScopeType::eLambda))) {
                break;
            }
            if (Token::Match(tok, "return|break|continue"))
                break;
            // Evaluate LHS of assignment before RHS
            if (Token* assignTok = assignExpr(tok)) {
                GenericAnalyzer::Action action = GenericAnalyzer::Action::None;
                Token* assignTop = assignTok;
                while(assignTop->isAssignmentOp()) {
                    action |= analyzeRecursive(assignTop->astOperand1());
                    if (!assignTop->astParent())
                        break;
                    assignTop = assignTop->astParent();
                }
                // TODO: Forward and reverse RHS
                if (action.isRead() || action.isModified()) {
                    if (!action.isModified())
                        valueFlowGenericForward(assignTop->astOperand1(), analyzer, settings);
                    break;
                }
                valueFlowGenericForward(assignTop->astOperand2(), analyzer, settings);
                tok = assignTop->previous();
                continue;
            }
            if (tok->str() == "}") {
                Token* condTok = getCondTokFromEnd(tok);
                if (!condTok)
                    break;
                // Evaluate condition of for and while loops first
                if (condTok && condTok->astTop() && Token::Match(condTok->astTop()->previous(), "for|while (")) {
                    GenericAnalyzer::Action action = analyzeRecursive(condTok);
                    if (action.isModified())
                        break;
                    valueFlowGenericForward(condTok, analyzer, settings);
                }
                const bool inElse = Token::simpleMatch(tok->link()->previous(), "else {");
                GenericAnalyzer::Action action = analyzeRange(tok->link(), tok);
                if (action.isModified())
                    analyzer->assume(condTok, !inElse, condTok);
                else if (action.isRead())
                    valueFlowGenericForward(tok->link(), tok, analyzer, settings);
                bool checkThen, checkElse;
                std::tie(checkThen, checkElse) = evalCond(condTok);
                if (inElse && checkThen)
                    break;
                if (!inElse && checkElse)
                    break;
                tok = condTok->astTop()->previous();
                continue;
            }
            if (tok->str() == "{") {
                if (tok->previous() &&
                (Token::simpleMatch(tok->previous(), "do") ||
                 (tok->strAt(-1) == ")" && Token::Match(tok->linkAt(-1)->previous(), "for|while (")))) {
                    GenericAnalyzer::Action action = analyzeRange(tok, tok->link());
                    if (action.isModified())
                        break;
                }
                if (Token::simpleMatch(tok->tokAt(-2), "} else {"))
                    tok = tok->linkAt(-2);
                if (Token::simpleMatch(tok->previous(), ") {"))
                    tok = tok->previous()->link();
                continue;
            }
            if (Token* next = isUnevaluated(tok)) {
                tok = next;
                continue;
            }
            if (Token* parent = isDeadCode(tok)) {
                tok = parent;
                continue;
            }
            if (!update(tok))
                break;
        }
    }

    static Token* assignExpr(Token* tok) {
        while (tok->astParent() && astIsRHS(tok)) {
            if (tok->astParent()->isAssignmentOp())
                return tok->astParent();
            tok = tok->astParent();
        }
        return nullptr;
    }

    static Token* isUnevaluated(Token* tok) {
        if (Token::Match(tok, ")|>") && tok->link()) {
            Token* start = tok->link();
            if (Token::Match(start->previous(), "sizeof|decltype ("))
                return start->previous();
            if (Token::simpleMatch(start, "<"))
                return start;
        }
        return nullptr;
    }

};

void valueFlowGenericReverse(Token* start,
        const ValuePtr<GenericAnalyzer>& a,
        const Settings* settings)
{
    ReverseTraversal rt{a, settings};
    rt.traverse(start);
}

