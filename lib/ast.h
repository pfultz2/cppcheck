/*
 * Cppcheck - A tool for static C/C++ code analysis
 * Copyright (C) 2007-2021 Cppcheck team.
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
#ifndef astH
#define astH
//---------------------------------------------------------------------------

#include <vector>

class Token;
class Settings;

struct AST {
    static AST parse(Token* tok, const Settings* settings);
    AST(Token* tok=nullptr);
    AST(Token* tok, AST op1);
    AST(Token* tok, AST op1, AST op2);
    bool failed() const;
    bool isPrefixUnary() const;
    bool isPostfixUnary() const;
    bool isBinary() const;
    void freeze() const;
    Token* tok;
    std::vector<AST> children;
    Token* next;
};

#endif
