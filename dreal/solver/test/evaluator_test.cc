#include "dreal/solver/evaluator.h"

#include <gtest/gtest.h>

namespace dreal {
namespace {

class EvaluatorTest : public ::testing::Test {
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

TEST_F(EvaluatorTest, Gt) {
  Evaluator evaluator{make_evaluator_quantifier_free(gt_, {x_, y_})};
  box_[x_] = 10.0;
  box_[y_] = 0.0;
  const Box::Interval result{evaluator(box_).evaluation()};
  std::cerr << gt_ << "\t" << evaluator << "\n" << result << std::endl;
  std::cerr << "-----------------------\n";
}

TEST_F(EvaluatorTest, Gte) {
  Evaluator evaluator{make_evaluator_quantifier_free(gte_, {x_, y_})};
  box_[x_] = 10.0;
  box_[y_] = 0.0;
  const Box::Interval result{evaluator(box_).evaluation()};
  std::cerr << gte_ << "\t" << evaluator << "\n" << result << std::endl;
  std::cerr << "-----------------------\n";
}

TEST_F(EvaluatorTest, Lt) {
  Evaluator evaluator{make_evaluator_quantifier_free(lt_, {x_, y_})};
  box_[x_] = 10.0;
  box_[y_] = 0.0;
  const Box::Interval result{evaluator(box_).evaluation()};
  std::cerr << lt_ << "\t" << evaluator << "\n" << result << std::endl;
  std::cerr << "-----------------------\n";
}

TEST_F(EvaluatorTest, Lte) {
  Evaluator evaluator{make_evaluator_quantifier_free(lte_, {x_, y_})};
  box_[x_] = 10.0;
  box_[y_] = 0.0;
  const Box::Interval result{evaluator(box_).evaluation()};
  std::cerr << lte_ << "\t" << evaluator << "\n" << result << std::endl;
  std::cerr << "-----------------------\n";
}

TEST_F(EvaluatorTest, Eq) {
  Evaluator evaluator{make_evaluator_quantifier_free(eq_, {x_, y_})};
  box_[x_] = 10.0;
  box_[y_] = 0.0;
  const Box::Interval result{evaluator(box_).evaluation()};
  std::cerr << eq_ << "\t" << evaluator << "\n" << result << std::endl;
  std::cerr << "-----------------------\n";
}

TEST_F(EvaluatorTest, Neq) {
  Evaluator evaluator{make_evaluator_quantifier_free(neq_, {x_, y_})};
  box_[x_] = 10.0;
  box_[y_] = 0.0;
  const Box::Interval result{evaluator(box_).evaluation()};
  std::cerr << neq_ << "\t" << evaluator << "\n" << result << std::endl;
  std::cerr << "-----------------------\n";
}

}  // namespace
}  // namespace dreal
