/*
 * Cppcheck - A tool for static C/C++ code analysis
 * Copyright (C) 2007-2018 Cppcheck team.
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


//---------------------------------------------------------------------------
#ifndef matcherH
#define matcherH
//---------------------------------------------------------------------------

#include <stdexcept>
#include <functional>
#include <string>
#include <unordered_map>
#include <vector>

#include "token.h"

namespace Matcher {

struct Context
{
    std::unordered_map<std::string, const Token*> tokens;
    template<class T>
    void bind(std::string, const T*)
    {
        throw std::runtime_error("Type is not bindable");
    }
    void bind(std::string name, const Token* tok)
    {
        tokens[name] = tok;
    }
};

template<class T, class R=T, class F=std::function<const R*(Context&, const T*)>>
struct Matcher
{
    F match;

    struct BindMatcher
    {
        F m;
        std::string name;

        const R* operator()(Context& ctx, const T* x) const
        {
            const R* result = m(ctx, x);
            if(result)
                ctx.bind(name, x);
            return result;
        }
    };

    // Setup binding tokens
    Matcher<T, R, BindMatcher> bind(std::string name) const 
    {
        return Matcher<T, R, BindMatcher>{BindMatcher{match, std::move(name)}};
    }

    template<class G>
    struct SubMatcher
    {
        F m;
        G subMatch;

        const R* operator()(Context& ctx, const T* x) const
        {
            const R* result = m(ctx, x);
            if(result && subMatch.match(ctx, result))
                return result;
            else
                return nullptr;
        }
    };

    // Compose a submatch
    template<class U, class G>
    Matcher<T, R, SubMatcher<Matcher<R, U, G>>> operator()(Matcher<R, U, G> subMatch) const
    {
        return Matcher<T, R, SubMatcher<Matcher<R, U, G>>>{SubMatcher<Matcher<R, U, G>>{match, subMatch}};
    }
};

struct Result
{
    const Token* tok;
    std::unordered_map<std::string, const Token*> tokens;
};

template<class F>
Result astMatch(const Token* tok, Matcher<Token, Token, F> m)
{
    Result result;
    Context ctx;
    result.tok = m.match(ctx, tok);
    result.tokens = ctx.tokens;
    return result;
}

Matcher<Token> pattern(std::string p)
{
    return Matcher<Token>{[=](Context&, const Token* tok) -> const Token* {
        if(Token::Match(tok, p.c_str()))
            return tok;
        else
            return nullptr;
    }};
}

Matcher<Token> binary(Matcher<Token> op1, Matcher<Token> op2)
{
    return Matcher<Token>{[=](Context& ctx, const Token* tok) -> const Token* {
        if(!tok->astOperand1() && !tok->astOperand2())
            return nullptr;
        if(op1.match(ctx, tok->astOperand1()) && op2.match(ctx, tok->astOperand2()))
            return tok;
        return nullptr;
    }};
}

}

#endif
