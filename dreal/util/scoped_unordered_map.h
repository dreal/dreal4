#pragma once

#include <functional>
#include <iostream>
#include <memory>
#include <tuple>
#include <unordered_map>
#include <utility>
#include <vector>

#include "dreal/util/exception.h"

namespace dreal {

/// Backtrackable map.
template <class Key, class T, class Hash = std::hash<Key>,
          class KeyEqual = std::equal_to<Key>,
          class Allocator = std::allocator<std::pair<const Key, T>>>
class ScopedUnorderedMap {
 public:
  // Aliases.
  using UnorderedMapType =
      std::unordered_map<Key, T, Hash, KeyEqual, Allocator>;
  using value_type = typename UnorderedMapType::value_type;
  using size_type = typename UnorderedMapType::size_type;
  using const_iterator = typename UnorderedMapType::const_iterator;

  // To backtrack, we need to record the actions applied to this
  // container.
  enum class ActionKind {
    INSERT,  ///< Insert(k, v) means that (k, v) is inserted.
    UPDATE,  ///< Update(k, v) means that (k, v) was replaced by a new value.
  };
  using Action = std::tuple<ActionKind, Key, T>;

  ScopedUnorderedMap() = default;
  ScopedUnorderedMap(const ScopedUnorderedMap&) = default;
  ScopedUnorderedMap(ScopedUnorderedMap&&) noexcept = default;
  ScopedUnorderedMap& operator=(const ScopedUnorderedMap&) = default;
  ScopedUnorderedMap& operator=(ScopedUnorderedMap&&) noexcept = default;
  ~ScopedUnorderedMap() = default;

  // Iterators.
  //
  // @note We only provide 'const' iterators because any modification
  // should be done explicitly via its APIs so that we can keep track
  // of changes and undo when pop() is called.
  const_iterator begin() const { return map_.begin(); }
  const_iterator cbegin() const { return map_.cbegin(); }
  const_iterator end() const { return map_.end(); }
  const_iterator cend() const { return map_.cend(); }

  // Capacity
  bool empty() const { return map_.empty(); }
  size_type size() const { return map_.size(); }

  // Modifiers
  void clear() {
    map_.clear();
    actions_.clear();
    stack_.clear();
  }
  void insert(const Key& k, const T& v) {
    auto it = map_.find(k);
    if (it == map_.end()) {
      // Case 1) k does not exist.
      actions_.emplace_back(ActionKind::INSERT, k, v);
      map_.emplace(k, v);
    } else {
      // Case 2) k exists. Save the old value so that we can roll
      // back later.
      actions_.emplace_back(ActionKind::UPDATE, k, it->second);
      it->second = v;  // Perform Update.
    }
  }

  // Lookup
  const T& operator[](const Key& key) const {
    const auto it = map_.find(key);
    if (it == map_.end()) {
      throw DREAL_RUNTIME_ERROR(
          "ScopedUnorderedMap has no entry for the key {}.", key);
    } else {
      return it->second;
    }
  }
  size_type count(const Key& key) const { return map_.count(key); }
  // @note It returns 'const' iterator.
  const_iterator find(const Key& key) const { return map_.find(key); }

  // Push/Pop
  void push() { stack_.push_back(actions_.size()); }
  void pop() {
    if (stack_.empty()) {
      throw DREAL_RUNTIME_ERROR(
          "ScopedUnorderedMap cannot be popped because it's scope is empty.");
    }
    size_type idx = stack_.back();
    while (idx < actions_.size()) {
      const Action& item{actions_.back()};
      const ActionKind kind{std::get<0>(item)};
      const Key& k{std::get<1>(item)};
      const T& v{std::get<2>(item)};
      auto it = map_.find(k);
      switch (kind) {
        case ActionKind::INSERT:
          // Remove (k, v).
          map_.erase(it);
          break;
        case ActionKind::UPDATE:
          // Roll back to map_[k] = v.
          it->second = v;
          break;
      }
      actions_.pop_back();
    }
    stack_.pop_back();
  }

 private:
  std::vector<Action> actions_;
  std::vector<size_type> stack_;
  UnorderedMapType map_;
};
}  // namespace dreal
