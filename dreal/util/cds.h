/*
   Copyright 2017 Toyota Research Institute

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*/
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
