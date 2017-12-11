#include "dreal/solver/formula_evaluator.h"

#include <iostream>

#include <gtest/gtest.h>

namespace dreal {
namespace {

using std::cerr;
using std::endl;

class FormulaEvaluatorTest : public ::testing::Test {
 protected:
  void SetUp() override {
    box_.Add(x_);
    box_.Add(y_);
    box_.Add(z_);
  }

  const Variable x_{"x"};
  const Variable y_{"y"};
  const Variable z_{"z"};

  const Formula gt_{x_ > y_};
  const Formula gte_{x_ >= y_};
  const Formula lt_{x_ < y_};
  const Formula lte_{x_ <= y_};
  const Formula eq_{x_ == y_};
  const Formula neq_{x_ != y_};

  Box box_;
};

TEST_F(FormulaEvaluatorTest, Gt) {
  FormulaEvaluator formula_evaluator{make_relational_formula_evaluator(gt_)};
  box_[x_] = 10.0;
  box_[y_] = 0.0;
  const Box::Interval result{formula_evaluator(box_).evaluation()};
  cerr << gt_ << "\t" << formula_evaluator << "\n" << result << endl;
  cerr << "-----------------------\n";
}

TEST_F(FormulaEvaluatorTest, Gte) {
  FormulaEvaluator formula_evaluator{make_relational_formula_evaluator(gte_)};
  box_[x_] = 10.0;
  box_[y_] = 0.0;
  const Box::Interval result{formula_evaluator(box_).evaluation()};
  cerr << gte_ << "\t" << formula_evaluator << "\n" << result << endl;
  cerr << "-----------------------\n";
}

TEST_F(FormulaEvaluatorTest, Lt) {
  FormulaEvaluator formula_evaluator{make_relational_formula_evaluator(lt_)};
  box_[x_] = 10.0;
  box_[y_] = 0.0;
  const Box::Interval result{formula_evaluator(box_).evaluation()};
  cerr << lt_ << "\t" << formula_evaluator << "\n" << result << endl;
  cerr << "-----------------------\n";
}

TEST_F(FormulaEvaluatorTest, Lte) {
  FormulaEvaluator formula_evaluator{make_relational_formula_evaluator(lte_)};
  box_[x_] = 10.0;
  box_[y_] = 0.0;
  const Box::Interval result{formula_evaluator(box_).evaluation()};
  cerr << lte_ << "\t" << formula_evaluator << "\n" << result << endl;
  cerr << "-----------------------\n";
}

TEST_F(FormulaEvaluatorTest, Eq) {
  FormulaEvaluator formula_evaluator{make_relational_formula_evaluator(eq_)};
  box_[x_] = 10.0;
  box_[y_] = 0.0;
  const Box::Interval result{formula_evaluator(box_).evaluation()};
  cerr << eq_ << "\t" << formula_evaluator << "\n" << result << endl;
  cerr << "-----------------------\n";
}

TEST_F(FormulaEvaluatorTest, Neq) {
  FormulaEvaluator formula_evaluator{make_relational_formula_evaluator(neq_)};
  box_[x_] = 10.0;
  box_[y_] = 0.0;
  const Box::Interval result{formula_evaluator(box_).evaluation()};
  cerr << neq_ << "\t" << formula_evaluator << "\n" << result << endl;
  cerr << "-----------------------\n";
}

}  // namespace
}  // namespace dreal
