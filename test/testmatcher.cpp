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


#include "matcher.h"
#include "settings.h"
#include "testsuite.h"
#include "token.h"
#include "tokenize.h"
#include "tokenlist.h"


class TestMatcher : public TestFixture {
public:
    TestMatcher() : TestFixture("TestMatcher") {
    }

private:

    void run() override {
        TEST_CASE(testPattern);
        TEST_CASE(testBinary);
    }

    template<class M>
    Matcher::Result astMatch(const char code[], M m) {
        Settings settings;
        Tokenizer tokenizer(&settings, this);
        std::istringstream istr(code);
        tokenizer.tokenize(istr, "test.cpp");
        for (const Token *tok = tokenizer.tokens(); tok; tok = tok->next()) {
            Matcher::Result mr = Matcher::astMatch(tok, m);
            if(mr.tok)
                return mr;
        }
        return Matcher::Result{};
    }

    void testPattern() {
        Matcher::Result mr;
        mr = astMatch("1 + x", Matcher::pattern("+"));
        ASSERT_EQUALS(true, mr.tok->str() == "+");

        mr = astMatch("1 + x", Matcher::pattern("%name%"));
        ASSERT_EQUALS(true, mr.tok->str() == "x");

        mr = astMatch("1 + x", Matcher::pattern("-"));
        ASSERT_EQUALS(true, mr.tok == nullptr);
    }

    void testBinary() {
        Matcher::Result mr;
        mr = astMatch("1 + x", Matcher::pattern("+")(Matcher::binary(Matcher::pattern("%num%"), Matcher::pattern("%name%"))));
        ASSERT_EQUALS(true, mr.tok->str() == "+");

        mr = astMatch("1 + x", Matcher::pattern("+")(Matcher::binary(Matcher::pattern("%name%"), Matcher::pattern("%name%"))));
        ASSERT_EQUALS(true, mr.tok == nullptr);
    }

};

REGISTER_TEST(TestMatcher)
