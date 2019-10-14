#include "dreal/util/scoped_vector.h"

#include <iostream>
#include <vector>

#include <gtest/gtest.h>

namespace dreal {
namespace {

using std::vector;

// Push each element of vector<int> to scoped_vector<int> and check if
// the two have the same elements.
GTEST_TEST(ScopedVector, PushBack) {
  const vector<int> vec{1, 2, 3, 4, 5, 6, 7, 8, 9, 10};

  ScopedVector<int> scoped_vector{};
  for (const auto& item : vec) {
    scoped_vector.push_back(item);
  }

  EXPECT_EQ(vec, scoped_vector.get_vector());
}

GTEST_TEST(ScopedVector, Push) {
  ScopedVector<int> scoped_vector{};

  scoped_vector.push_back(1);
  scoped_vector.push_back(2);
  scoped_vector.push_back(3);

  // First push.
  scoped_vector.push();

  scoped_vector.push_back(4);
  scoped_vector.push_back(5);
  scoped_vector.push_back(6);

  // Second push.
  scoped_vector.push();

  // Third push. Note that there is no push_back operation between 2nd
  // and 3rd pushes.
  scoped_vector.push();

  scoped_vector.push_back(7);
  scoped_vector.push_back(8);
  scoped_vector.push_back(9);

  // It should include {1,2,3,4,5,6,7,8,9}.
  EXPECT_EQ(scoped_vector.size(), 9U);
  EXPECT_EQ(scoped_vector.get_vector(),
            vector<int>({1, 2, 3, 4, 5, 6, 7, 8, 9}));

  // After pop, it should include {1,2,3,4,5,6}.
  scoped_vector.pop();
  EXPECT_EQ(scoped_vector.size(), 6U);
  EXPECT_EQ(scoped_vector.get_vector(), vector<int>({1, 2, 3, 4, 5, 6}));

  // After pop, it should still include {1,2,3,4,5,6}.
  scoped_vector.pop();
  EXPECT_EQ(scoped_vector.size(), 6U);
  EXPECT_EQ(scoped_vector.get_vector(), vector<int>({1, 2, 3, 4, 5, 6}));

  // After pop, it should include {1,2,3}.
  scoped_vector.pop();
  EXPECT_EQ(scoped_vector.size(), 3U);
  EXPECT_EQ(scoped_vector.get_vector(), vector<int>({1, 2, 3}));

  // There should be nothing to pop and it throws runtime_error.
  EXPECT_THROW(scoped_vector.pop(), std::runtime_error);
}

}  // namespace
}  // namespace dreal
