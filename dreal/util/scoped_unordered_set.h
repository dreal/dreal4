#pragma once

#include <functional>
#include <iostream>
#include <memory>
#include <tuple>
#include <unordered_set>
#include <utility>
#include <vector>

#include "dreal/util/exception.h"

namespace dreal {

/// Backtrackable set.

template <class Key, class Hash = std::hash<Key>,
          class KeyEqual = std::equal_to<Key>,
          class Allocator = std::allocator<Key>>
class ScopedUnorderedSet {
 public:
  /// Aliases.
  using UnorderedSetType = std::unordered_set<Key, Hash, KeyEqual, Allocator>;
  using key_type = typename UnorderedSetType::key_type;
  using value_type = typename UnorderedSetType::value_type;
  using size_type = typename UnorderedSetType::size_type;
  using const_iterator = typename UnorderedSetType::const_iterator;

  /// To backtrack, we need to record the actions applied to this
  /// container.
  enum class ActionKind {
    INSERT,  ///< Insert(k) means that k is inserted.
  };
  using Action = std::tuple<ActionKind, Key>;

  ScopedUnorderedSet() = default;
  ScopedUnorderedSet(const ScopedUnorderedSet&) = default;
  ScopedUnorderedSet(ScopedUnorderedSet&&) noexcept = default;
  ScopedUnorderedSet& operator=(const ScopedUnorderedSet&) = default;
  ScopedUnorderedSet& operator=(ScopedUnorderedSet&&) noexcept = default;
  ~ScopedUnorderedSet() = default;

  /// Iterators.
  ///
  /// @note We only provide 'const' iterators because any modification
  /// should be done explicitly via its APIs so that we can keep track
  /// of changes and undo when pop() is called.
  const_iterator begin() const { return set_.begin(); }
  const_iterator cbegin() const { return set_.cbegin(); }
  const_iterator end() const { return set_.end(); }
  const_iterator cend() const { return set_.cend(); }

  /// Capacity
  bool empty() const { return set_.empty(); }
  size_type size() const { return set_.size(); }

  /// Modifiers
  void clear() {
    set_.clear();
    actions_.clear();
    stack_.clear();
  }
  void insert(const Key& k) {
    auto it = set_.find(k);
    if (it == set_.end()) {
      // Case 1) k does not exist.
      actions_.emplace_back(ActionKind::INSERT, k);
      set_.emplace(k);
    }
  }

  size_type count(const Key& key) const { return set_.count(key); }
  /// @note It returns 'const' iterator.
  const_iterator find(const Key& key) const { return set_.find(key); }

  /// Push/Pop
  void push() { stack_.push_back(actions_.size()); }
  void pop() {
    if (stack_.empty()) {
      throw DREAL_RUNTIME_ERROR(
          "ScopedUnorderedSet cannot be popped because it's scope is empty.");
    }
    size_type idx = stack_.back();
    while (idx < actions_.size()) {
      const Action& item{actions_.back()};
      const ActionKind kind{std::get<0>(item)};
      const Key& k{std::get<1>(item)};
      auto it = set_.find(k);
      switch (kind) {
        case ActionKind::INSERT:
          // Remove k.
          set_.erase(it);
          break;
      }
      actions_.pop_back();
    }
    stack_.pop_back();
  }

 private:
  std::vector<Action> actions_;
  std::vector<size_type> stack_;
  UnorderedSetType set_;
};
}  // namespace dreal
