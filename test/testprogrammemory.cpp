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

#include "config.h"
#include "fixture.h"
#include "helpers.h"
#include "mathlib.h"
#include "settings.h"
#include "token.h"
#include "programmemory.h"
#include "utils.h"
#include "vfvalue.h"

#include <algorithm>
#include <cstddef>
#include <stdexcept>
#include <string>
#include <vector>

class TestProgramMemory : public TestFixture {
public:
    TestProgramMemory() : TestFixture("TestProgramMemory") {}

private:
    const Settings settings = settingsBuilder().library("std.cfg").build();

    void run() override {
        TEST_CASE(copyOnWrite);
        TEST_CASE(hasValue);
        TEST_CASE(getValue);
        TEST_CASE(at);
        TEST_CASE(setValueConstraints);
        TEST_CASE(setValueReplacesConstraints);
        TEST_CASE(containerEmpty);
        TEST_CASE(executeRange);
        TEST_CASE(executeContainerSizeRange);
    }

    static ValueFlow::Value impossible(MathLib::bigint x, ValueFlow::Value::Bound bound = ValueFlow::Value::Bound::Point) {
        ValueFlow::Value v{x, bound};
        v.setImpossible();
        return v;
    }

    // The constraint "x > lower": the values up to lower are impossible
    static ValueFlow::Value greaterThan(MathLib::bigint lower) {
        return impossible(lower, ValueFlow::Value::Bound::Upper);
    }

    // The constraint "x < upper": the values from upper on are impossible
    static ValueFlow::Value lessThan(MathLib::bigint upper) {
        return impossible(upper, ValueFlow::Value::Bound::Lower);
    }

    static ValueFlow::Value containerSize(ValueFlow::Value v) {
        v.valueType = ValueFlow::Value::ValueType::CONTAINER_SIZE;
        return v;
    }

    static const ValueFlow::Value* findValue(const ProgramMemory::Values& values, MathLib::bigint x, ValueFlow::Value::Bound bound) {
        const auto it = std::find_if(values.cbegin(), values.cend(), [&](const ValueFlow::Value& v) {
            return v.intvalue == x && v.bound == bound;
        });
        return it == values.cend() ? nullptr : &*it;
    }

    void copyOnWrite() const {
        SimpleTokenList tokenlist("1+1;\n");
        Token* tok = tokenlist.front();
        const nonneg int id = 123;
        tok->exprId(id);

        ProgramMemory pm;
        const ValueFlow::Value* v = pm.getValue(id);
        ASSERT(!v);
        pm.setValue(tok, ValueFlow::Value{41});

        v = pm.getValue(id);
        ASSERT(v);
        ASSERT_EQUALS(41, v->intvalue);

        // create a copy
        ProgramMemory pm2 = pm;

        // make sure the value was copied
        v = pm2.getValue(id);
        ASSERT(v);
        ASSERT_EQUALS(41, v->intvalue);

        // set a value in the copy to trigger copy-on-write
        pm2.setValue(tok, ValueFlow::Value{42});

        // make another copy and set another value
        ProgramMemory pm3 = pm2;

        // set a value in the copy to trigger copy-on-write
        pm3.setValue(tok, ValueFlow::Value{43});

        // make sure the value was set
        v = pm2.getValue(id);
        ASSERT(v);
        ASSERT_EQUALS(42, v->intvalue);

        // make sure the value was set
        v = pm3.getValue(id);
        ASSERT(v);
        ASSERT_EQUALS(43, v->intvalue);

        // make sure the original value remains unchanged
        v = pm.getValue(id);
        ASSERT(v);
        ASSERT_EQUALS(41, v->intvalue);
    }

    void hasValue() const {
        ProgramMemory pm;
        ASSERT(!pm.hasValue(123));
    }

    void getValue() const {
        ProgramMemory pm;
        ASSERT(!pm.getValue(123));
        ASSERT(!pm.getValues(123));
    }

    void at() const {
        ProgramMemory pm;
        ASSERT_THROW_EQUALS(pm.at(123), std::out_of_range, "ProgramMemory::at");
        ASSERT_THROW_EQUALS(utils::as_const(pm).at(123), std::out_of_range, "ProgramMemory::at");
    }

    void setValueConstraints() const {
        SimpleTokenList tokenlist("1+1;\n");
        Token* tok = tokenlist.front();
        const nonneg int id = 123;
        tok->exprId(id);

        ProgramMemory pm;
        // x > 3 and x < 10 hold at the same time
        pm.setValue(tok, greaterThan(3));
        pm.setValue(tok, lessThan(10));
        const ProgramMemory::Values* values = pm.getValues(id);
        ASSERT(values);
        ASSERT_EQUALS(2U, values->size());
        ASSERT(findValue(*values, 3, ValueFlow::Value::Bound::Upper));
        ASSERT(findValue(*values, 10, ValueFlow::Value::Bound::Lower));

        // several constraints are not a single value
        ASSERT(!pm.getValue(id));
        ASSERT(!pm.getValue(id, true));
        MathLib::bigint i = 0;
        ASSERT(!pm.getIntValue(id, i));

        // a repeated constraint is not added again
        pm.setValue(tok, greaterThan(3));
        ASSERT_EQUALS(2U, pm.at(id).size());

        // a weaker bound is dropped
        pm.setValue(tok, greaterThan(1));
        ASSERT_EQUALS(2U, pm.at(id).size());
        ASSERT(findValue(pm.at(id), 3, ValueFlow::Value::Bound::Upper));

        // a stronger bound replaces the bound
        pm.setValue(tok, greaterThan(5));
        ASSERT_EQUALS(2U, pm.at(id).size());
        ASSERT(findValue(pm.at(id), 5, ValueFlow::Value::Bound::Upper));
        ASSERT(!findValue(pm.at(id), 3, ValueFlow::Value::Bound::Upper));

        // an impossible value inside the range is kept
        pm.setValue(tok, impossible(7));
        ASSERT_EQUALS(3U, pm.at(id).size());
        ASSERT(findValue(pm.at(id), 7, ValueFlow::Value::Bound::Point));

        // x > 5 and x != 6 is x > 6, and then x != 7 makes it x > 7
        pm.setValue(tok, impossible(6));
        ASSERT_EQUALS(2U, pm.at(id).size());
        ASSERT(findValue(pm.at(id), 7, ValueFlow::Value::Bound::Upper));
        ASSERT(findValue(pm.at(id), 10, ValueFlow::Value::Bound::Lower));
    }

    void setValueReplacesConstraints() const {
        SimpleTokenList tokenlist("1+1;\n");
        Token* tok = tokenlist.front();
        const nonneg int id = 123;
        tok->exprId(id);

        ProgramMemory pm;
        pm.setValue(tok, greaterThan(3));
        pm.setValue(tok, lessThan(10));

        // a value of the expression replaces its constraints
        pm.setValue(tok, ValueFlow::Value{5});
        MathLib::bigint i = 0;
        ASSERT(pm.getIntValue(id, i));
        ASSERT_EQUALS(5, i);
        ASSERT_EQUALS(1U, pm.at(id).size());

        // a constraint the value satisfies keeps the value
        pm.setValue(tok, greaterThan(3));
        pm.setValue(tok, impossible(7));
        ASSERT(pm.getIntValue(id, i));
        ASSERT_EQUALS(5, i);

        // a constraint the value violates replaces the value
        pm.setValue(tok, impossible(5));
        ASSERT(!pm.getIntValue(id, i));
        ASSERT_EQUALS(1U, pm.at(id).size());
        ASSERT(pm.at(id).front().isImpossible());

        // a possible value with a bound is a value of the expression
        pm.setValue(tok, ValueFlow::Value{4, ValueFlow::Value::Bound::Lower});
        ASSERT(pm.getIntValue(id, i));
        ASSERT_EQUALS(4, i);

        // a value of another type replaces the value
        pm.setValue(tok, containerSize(ValueFlow::Value{3}));
        ASSERT(!pm.getIntValue(id, i));
        ASSERT(pm.getContainerSizeValue(id, i));
        ASSERT_EQUALS(3, i);

        pm.setUnknown(tok);
        ASSERT(pm.hasValue(id));
        ASSERT(pm.getValue(id));
        ASSERT(pm.getValue(id)->isUninitValue());
    }

    void containerEmpty() const {
        SimpleTokenList tokenlist("1+1;\n");
        Token* tok = tokenlist.front();
        const nonneg int id = 123;
        tok->exprId(id);

        ProgramMemory pm;
        MathLib::bigint empty = -1;
        ASSERT(!pm.getContainerEmptyValue(id, empty));

        pm.setContainerSizeValue(tok, 0);
        ASSERT(pm.getContainerEmptyValue(id, empty));
        ASSERT_EQUALS(1, empty);

        pm.setContainerSizeValue(tok, 3);
        ASSERT(pm.getContainerEmptyValue(id, empty));
        ASSERT_EQUALS(0, empty);

        // size != 0
        pm.clear();
        pm.setContainerSizeValue(tok, 0, false);
        ASSERT(pm.getContainerEmptyValue(id, empty));
        ASSERT_EQUALS(0, empty);

        // size > 2
        pm.clear();
        pm.setValue(tok, containerSize(greaterThan(2)));
        ASSERT(pm.getContainerEmptyValue(id, empty));
        ASSERT_EQUALS(0, empty);

        // size < 1
        pm.clear();
        pm.setValue(tok, containerSize(lessThan(1)));
        ASSERT(pm.getContainerEmptyValue(id, empty));
        ASSERT_EQUALS(1, empty);

        // size < 5 does not decide it
        pm.clear();
        pm.setValue(tok, containerSize(lessThan(5)));
        ASSERT(!pm.getContainerEmptyValue(id, empty));
    }

    // Remove the values ValueFlow attached to the tokens, so that only the program memory decides
    static void clearValues(SimpleTokenizer& tokenizer) {
        for (Token* tok = tokenizer.list.front(); tok; tok = tok->next())
            tok->clearValueFlow();
    }

    // The right hand sides of the assignments to the variable, in order
    static std::vector<const Token*> assignedExpressions(const Token* tokens, const std::string& var) {
        std::vector<const Token*> result;
        for (const Token* tok = tokens; tok; tok = tok->next()) {
            if (tok->str() == "=" && tok->astOperand1() && tok->astOperand1()->str() == var && tok->astOperand2())
                result.push_back(tok->astOperand2());
        }
        return result;
    }

    // Evaluate the expression with the program memory built from the conditions enclosing it.
    // The result as a string, empty if it is unknown.
    std::string evaluate(const Token* expr) const {
        ProgramMemoryState pms(settings);
        pms.addState(expr, {});
        ProgramMemory pm = pms.state;
        MathLib::bigint result = 0;
        bool error = false;
        execute(expr, pm, &result, &error, settings);
        if (error)
            return "";
        return std::to_string(result);
    }

    void executeRange() {
        const char code[] = "void f(int x, int y) {\n"
                            "    if (x > 3) {\n"
                            "        if (x < 10) {\n"
                            "            y = x == 15;\n"
                            "            y = x == 5;\n"
                            "            y = x < 20;\n"
                            "            y = x >= 4;\n"
                            "            y = x + 1 > 4;\n"
                            "            y = 10 - x < 7;\n"
                            "            y = -x < 0;\n"
                            "            y = x;\n"
                            "        }\n"
                            "    }\n"
                            "}\n";
        SimpleTokenizer tokenizer(settings, *this);
        ASSERT(tokenizer.tokenize(code));
        clearValues(tokenizer);
        const std::vector<const Token*> exprs = assignedExpressions(tokenizer.tokens(), "y");
        ASSERT_EQUALS(8U, exprs.size());
        // 3 < x < 10
        ASSERT_EQUALS("0", evaluate(exprs[0]));
        ASSERT_EQUALS("", evaluate(exprs[1]));
        ASSERT_EQUALS("1", evaluate(exprs[2]));
        ASSERT_EQUALS("1", evaluate(exprs[3]));
        // the range is shifted by arithmetic
        ASSERT_EQUALS("1", evaluate(exprs[4]));
        ASSERT_EQUALS("1", evaluate(exprs[5]));
        ASSERT_EQUALS("1", evaluate(exprs[6]));
        // a range is not a value
        ASSERT_EQUALS("", evaluate(exprs[7]));
    }

    void executeContainerSizeRange() {
        const char code[] = "void f(std::string s, bool y) {\n"
                            "    if (s.size() > 3) {\n"
                            "        if (s.size() < 10) {\n"
                            "            y = s.size() == 15;\n"
                            "            y = s.size() < 20;\n"
                            "            y = s.empty();\n"
                            "            y = s.size() == 5;\n"
                            "        }\n"
                            "    }\n"
                            "}\n";
        SimpleTokenizer tokenizer(settings, *this);
        ASSERT(tokenizer.tokenize(code));
        clearValues(tokenizer);
        const std::vector<const Token*> exprs = assignedExpressions(tokenizer.tokens(), "y");
        ASSERT_EQUALS(4U, exprs.size());
        // 3 < s.size() < 10
        ASSERT_EQUALS("0", evaluate(exprs[0]));
        ASSERT_EQUALS("1", evaluate(exprs[1]));
        ASSERT_EQUALS("0", evaluate(exprs[2]));
        ASSERT_EQUALS("", evaluate(exprs[3]));
    }
};

REGISTER_TEST(TestProgramMemory)
