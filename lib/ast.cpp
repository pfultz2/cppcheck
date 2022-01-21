#include "ast.h"
#include "token.h"
#include "settings.h"

#include <array>

AST::AST(Token* tok, Token* next)
: tok(tok), next(next) {
    if (tok && !next)
        next = tok->next();
}
AST::AST(Token* tok, AST op1)
: tok(tok), children({std::move(op1)}) {
    next = children.back().next;
}
AST::AST(Token* tok, AST op1, AST op2)
: tok(tok), children({std::move(op1), std::move(op2)}) {
    next = children.back().next;
}

bool AST::failed() const
{
    return tok == nullptr;
}

bool AST::empty() const
{
    return !failed() && tok == next;
}

bool AST::isPrefixUnary() const
{
    if (children.size() == 2)
        return children.front().failed();
    return failed();
}
bool AST::isPostfixUnary() const
{
    return children.size() == 1;
}
bool AST::isBinary() const
{
    return children.size() == 2 && !children.front().failed();
}

void AST::freeze() const
{
    for(const AST& child:children)
        child.freeze();
    if (!tok)
        return;
    if (children.size() > 0)
        tok->astOperand1(children[0].tok);
    if (children.size() > 1) {
        tok->astOperand2(children[1].tok);
    }
}

int getPrecedence(const AST& ast)
{
    if (Token::Match(ast.tok, "::"))
        return 1;
    // TODO: Check for c casts
    if (Token::Match(ast.tok, "{|[|.|("))
        return 2;
    if (ast.isPostfixUnary() && Token::Match(ast.tok, "++|--"))
        return 2;
    if (ast.isPrefixUnary() && Token::Match(ast.tok, "++|--|+|-|!|~|*|&"))
        return 3;
    if (Token::Match(ast.tok, ".*"))
        return 4;
    if (Token::Match(ast.tok, "*|/|%"))
        return 5;
    if (Token::Match(ast.tok, "+|-"))
        return 6;
    if (Token::Match(ast.tok, "<<|>>"))
        return 7;
    if (Token::Match(ast.tok, "<=>"))
        return 8;
    if (Token::Match(ast.tok, "<|<=|>|>="))
        return 9;
    if (Token::Match(ast.tok, "==|!="))
        return 10;
    if (Token::simpleMatch(ast.tok, "&"))
        return 11;
    if (Token::simpleMatch(ast.tok, "|"))
        return 12;
    if (Token::simpleMatch(ast.tok, "&&"))
        return 13;
    if (Token::simpleMatch(ast.tok, "||"))
        return 14;
    if (Token::Match(ast.tok, "?|:|throw|%assign%"))
        return 15;
    if (Token::simpleMatch(ast.tok, ","))
        return 16;
    return 0;
}

AST compilePrecedence(AST ast) {
    int p = getPrecedence(ast);
    for(const AST& child:ast.children)
        if (getPrecedence(child) < p)
            return AST{};
    return ast;
}

struct ParserEngine;
using AnyRule2 = std::function<AST(ParserEngine&, Token*)>;
struct ParserEngine {
    template<class Rule>
    AST parse(Token* tok, Rule rule) {
        if (tok)
            return rule(*this, tok);
        return AST{};
    }
    AST If(Token* tok, bool b) {
        if (b) {
            return AST{tok};
        }
        return AST{};
    }
    template<class... Rules>
    std::array<AST, sizeof...(Rules)> sequence(Token* tok, Rules... rules) {
        Token* next = tok;
        auto each = [&](AnyRule2 rule) -> AST {
            AST a = parse(next, rule);
            next = a.next;
            return a;
        };
        return std::array<AST, sizeof...(Rules)>{each(rules)...};
    }
    template<class OpRule, class Rule>
    AST prefixOp(Token* tok, OpRule opRule, Rule rule) {
        auto asts = sequence(tok, opRule, rule);
        if (asts.back().failed())
            return asts.back();
        return AST{tok, AST{}, asts.back()};
    }
    template<class OpRule, class Rule>
    AST postfixOp(Token* tok, Rule rule, OpRule opRule) {
        auto asts = sequence(tok, rule, opRule);
        if (asts.back().failed())
            return asts.back();
        return AST{tok, asts.back()};
    }
    template<class Rule1, class OpRule, class Rule2>
    AST infixOp(Token* tok, Rule1 rule1, OpRule opRule, Rule2 rule2) {
        auto asts = sequence(tok, rule1, opRule, rule2);
        if (asts.back().failed())
            return asts.back();
        return AST{asts[1].tok, asts[0], asts[2]};
    }
    // rule (opRule rule)*
    template<class Rule, class OpRule>
    AST binOp(Token* tok, Rule rule, OpRule opRule) {
        return infixOp(tok, rule, opRule, [=](ParserEngine& pe, Token* tok) { 
            return pe.binOp(tok, rule, opRule); 
        });
    }
    template<class Rule1, class Rule2>
    AST either(Token* tok, Rule1 rule1, Rule2 rule2) {
        AST ast1 = parse(tok, rule1);
        if (!ast1.failed())
            return ast1;
        return parse(tok, rule2);
    }

    template<class Rule, class... Rules>
    AST either(Token* tok, Rule rule, Rules... rules) {
        return either(tok, rule, [&](ParserEngine& pe, Token* tok) {
            return pe.either(tok, rules...);
        });
    }
};

template<class F>
struct Rule;

using AnyRule = Rule<std::function<AST(ParserEngine&, Token*)>>;

template<class F>
Rule<F> makeRule(const std::string&, F);

#define AUTO_RULE AnyRule

template<class F>
struct Rule
{
    std::string name;
    F f;

    Rule(std::string name, F f)
    : name(std::move(name)), f(std::move(f))
    {}

    template<class G>
    Rule(Rule<G> r)
    : name(std::move(r.name)), f(std::move(r.f))
    {}

    AST operator()(ParserEngine& pe, Token* tok) const
    {
        return f(pe, tok);
    }
    
    template<class Action>
    AUTO_RULE operator[](Action a) const
    {
        return makeRule(name, [f=f, a](ParserEngine& pe, Token* tok) {
            return a(f(pe, tok));
        });
    }

    template<class NextRule>
    AUTO_RULE operator >>(NextRule r) const
    {
        return makeRule(name + ">>" + r.name, [self=*this, r](ParserEngine& pe, Token* tok) -> AST {
            AST a = pe.parse(tok, self);
            if (a.failed())
                return a;
            AST b = pe.parse(a.next, r);
            if (b.failed())
                return b;
            if (a.empty())
                return AST{tok, b};
            else if (b.empty())
                return AST{tok, a};
            else
                return AST{tok, a, b};
        });
    }

    template<class NextRule>
    AUTO_RULE operator |(NextRule r) const
    {
        return makeRule(name + "|" + r.name, [self=*this, r](ParserEngine& pe, Token* tok) -> AST {
            AST a = pe.parse(tok, self);
            if (!a.failed())
                return a;
            return pe.parse(a.next, r);
        });
    }

    AUTO_RULE operator *() const
    {
        return makeRule("*" + name, [self=*this](ParserEngine& pe, Token* tok) -> AST {
            AST a{tok, tok};
            while(true) {
                AST b = pe.parse(tok, self);
                if (b.failed())
                    break;
                a.children.push_back(b);
            }
            return a;
        });
    }
    AUTO_RULE optional() const
    {
        return makeRule(name + "?", [self=*this](ParserEngine& pe, Token* tok) -> AST {
            AST a = pe.parse(tok, self);
            if (!a.failed())
                return a;
            return AST{tok, tok};
        });
    }

    Rule<F> rename(const std::string& newName) const
    {
        return Rule<F>{newName, f};
    }
};

AST convertToBinaryTree(AST a)
{
    
}

// rule (opRule rule)*
template<class Rule, class OpRule>
AUTO_RULE binOp(Rule rule, OpRule opRule)
{
    return rule >> *(opRule >> rule);
}

#define RULE(var, ...) auto var = (__VA_ARGS__).rename(#var)
#define PARSE_IF(tok, ...) makeRule(#__VA_ARGS__, [](ParserEngine& pe, Token* tok) { return pe.If(tok, __VA_ARGS__); })

AnyRule CreateGrammar()
{
    auto atom = PARSE_IF(tok, tok->isName() || tok->isLiteral());
    RULE(commaExpr, atom >> PARSE_IF(tok, Token::Match(tok, ",")) >> atom);
    RULE(expression, atom);
    return expression;
}

// #define RULE_IF(tok, m) +[](ParserEngine& pe, Token* tok) { return pe.If(tok, m); } 
// #define RULE_IF(tok, m) +[](ParserEngine& pe, Token* tok) { return pe.If(tok, m); } 


template<char C>
AST parseChar(ParserEngine& pe, Token* tok) {
    return pe.If(tok, tok->str() == std::string{C});
}
AST parseAtom(ParserEngine& pe, Token* tok) {
    return pe.If(tok, tok->isName() || tok->isLiteral());
}
AST parseAssignExpr(ParserEngine& pe, Token* tok);
// AST parseExpr(ParserEngine& pe, Token* tok) {
//     return pe.infixOp(tok, &parseAssignExpr, RULE_IF(tok2, tok2->str() == ","), &parseExpr);
// }
// AST parseExpr(ParserEngine& pe, Token* tok);
// AST parseOp(ParserEngine& pe, Token* tok) {
//     return pe.If(tok, Token::Match(tok, "%op%|(|{|[|::|:|?"));
// }
// AST parseBinaryOp(ParserEngine& pe, Token* tok) {
//     return compilePrecedence(pe.infixOp(tok, &parseExpr, &parseOp, &parseExpr));
// }
// AST parsePrefixOp(ParserEngine& pe, Token* tok) {
//     return compilePrecedence(pe.prefixOp(tok, &parseOp, &parseExpr));
// }
// AST parsePostfixOp(ParserEngine& pe, Token* tok) {
//     return compilePrecedence(pe.postfixOp(tok, &parseExpr, &parseOp));
// }
// AST parseOpExpr(ParserEngine& pe, Token* tok) {
//     return pe.either(tok, &parsePostfixOp, &parsePrefixOp, &parseBinaryOp, &parseAtom);
// }
// AST parseFunctionArgs(ParserEngine& pe, Token* tok) {
//     auto s = pe.sequence(tok, &parseChar<'('>, &parseExpr, &parseChar<')'>);

// }
// AST parseLambda(ParserEngine& pe, Token* tok) {
//     auto s = pe.sequence(tok, &parseChar<'['>, &parseExpr, &parseChar<']'>);
// }

static AST AST::parse(Token* tok, const Settings* settings)
{
    return AST{};
}
