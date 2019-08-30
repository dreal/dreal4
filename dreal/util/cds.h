#pragma once

#include <memory>

#include <cds/container/mspriority_queue.h>
#include <cds/container/treiber_stack.h>
#include <cds/gc/hp.h>
#include <cds/init.h>

namespace dreal {

using gc_type = cds::gc::HP;

template <typename T>
using Stack = cds::container::TreiberStack<gc_type, T>;

template <typename T, typename Comparator>
using PriorityQueue = cds::container::MSPriorityQueue<
    T, typename cds::container::mspriority_queue::make_traits<
           cds::opt::buffer<cds::opt::v::initialized_dynamic_buffer<char>>,
           cds::opt::compare<Comparator>>::type>;

class CdsScopeGuard {
 public:
  explicit CdsScopeGuard(bool use) : use_{use} {
    if (use_) {
      cds::threading::Manager::attachThread();
    }
  }
  CdsScopeGuard(const CdsScopeGuard&) = delete;
  CdsScopeGuard(CdsScopeGuard&&) = delete;
  CdsScopeGuard& operator=(const CdsScopeGuard&) = delete;
  CdsScopeGuard& operator=(CdsScopeGuard&&) = delete;

  ~CdsScopeGuard() {
    if (use_) {
      cds::threading::Manager::detachThread();
    }
  }

 private:
  const bool use_{};
};

class CdsInit {
 public:
  explicit CdsInit(bool use_lock_free_container) {
    // Initialize libcds
    cds::Initialize();
    hpGC_ = std::make_unique<gc_type>();
    if (use_lock_free_container) {
      cds::threading::Manager::attachThread();
    }
  }
  CdsInit(const CdsInit&) = delete;
  CdsInit(CdsInit&&) = delete;
  CdsInit& operator=(const CdsInit&) = delete;
  CdsInit& operator=(CdsInit&&) = delete;

  ~CdsInit() {
    // Terminate libcds
    cds::Terminate();
  }

 private:
  // Initialize Hazard Pointer singleton
  std::unique_ptr<gc_type> hpGC_;
};

}  // namespace dreal
