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
#include <cassert>
#include <ostream>
#include <random>
#include <string>
#include <vector>

#include "dreal/api/api.h"

using dreal::Config;
using dreal::Expression;
using dreal::Formula;
using dreal::Variable;

using std::cout;
using std::to_string;
using std::vector;

std::random_device rd;   // random seed
std::mt19937 gen(rd());  // random generator with rd()
// will turn gen into uniform distribution
std::uniform_real_distribution<> dis(-2.0, 2.0);

// bounds in input variables
Formula assign_bounds(const vector<Variable>& vars, double lb, double ub);

// generate network with random parameters
Formula generate_network(const vector<Variable>& vars,
                         const vector<Variable>& pars,
                         const vector<Variable>& outs, int depth, int width);

// set requirements on the output here
Formula set_property(const vector<Variable>&);

int main() {
  const int n = 3;     // number of input variables
  const int m = 1000;  // number of parameters
  const int k = 2;     // number of outputs
  const int d = 2;     // depth
  const int w = 4;     // width
  assert(d * w < m);
  vector<Variable> vars;  // all vars
  vector<Variable> pars;  // all parameters
  vector<Variable> outs;  // all outputs
  // initialize the variables
  vars.reserve(n);
  for (int i = 0; i < n; i++) {
    vars.emplace_back("x_" + to_string(i));
  }
  pars.reserve(m);
  for (int i = 0; i < m; i++) {
    pars.emplace_back("p_" + to_string(i));
  }
  outs.reserve(k);
  for (int i = 0; i < k; i++) {
    outs.emplace_back("y_" + to_string(i));
  }
  // configs for the solver
  Config config;
  config.mutable_precision() = 0.01;
  config.mutable_use_local_optimization() = true;
  // encode the network
  const Formula nn = generate_network(vars, pars, outs, d, w);
  // bounds on vars
  const Formula bounds = assign_bounds(vars, -2.0, 2.0);
  // property
  const Formula property = set_property(outs);
  // solve
  const auto result = CheckSatisfiability(bounds && nn && property, config);
  // output
  if (result) {
    cout << "\n"
         << "Result: Sat. The following assignment satisfies the conditions."
         << "\n"
         << *result << "\n";
  } else {
    cout << "\n"
         << "Result: Unsat."
         << "\n";
  }
}

Formula assign_bounds(const vector<Variable>& vars, const double lb,
                      const double ub) {
  assert(lb <= ub);
  Formula bounds;
  for (const auto& v : vars) {
    bounds = bounds && (v > lb) && (v < ub);
  }
  cout << "The following bounds were set: "
       << "\n"
       << bounds << "\n";
  return bounds;
}

Formula generate_network(const vector<Variable>& vars,
                         const vector<Variable>& pars,
                         const vector<Variable>& outs, const int depth,
                         const int width) {
  vector<Expression> layer_input;
  Formula param_assignment;
  double r;
  for (const auto& v : vars) {
    layer_input.emplace_back(v);
    cout << "Input variable: " << v << "\n";
  }
  int offset = 0;  // keep track of consumption of parameters
  for (int i = 0; i < depth; i++) {
    vector<Expression> layer_output;
    for (int j = 0; j < width; j++) {
      Expression single_output;
      for (const Expression& layer_input_k : layer_input) {
        single_output += layer_input_k * pars[offset];
        r = dis(gen);
        param_assignment = param_assignment &&
                           (pars[offset] == r);  // assign random value dis(gen)
        cout << "Weight assigned: " << pars[offset] << "=" << r << "\n";
        offset++;
      }
      // layer_output.push_back(tanh(single_output+pars[offset]));
      layer_output.push_back(tanh(single_output + pars[offset]));
      r = dis(gen);
      param_assignment = param_assignment && (pars[offset] == r);
      cout << "Weight assigned: " << pars[offset] << "=" << r << "\n";
      offset++;
    }
    layer_input = layer_output;
  }
  Formula nn;
  for (const auto& o : outs) {
    Expression single_output;
    for (const auto& layer_input_k : layer_input) {
      single_output += layer_input_k * pars[offset];
      r = dis(gen);
      param_assignment = param_assignment && (pars[offset] == r);
      cout << "Weight assigned: " << pars[offset] << "=" << r << "\n";
      offset++;
    }
    nn = nn && (o == single_output + pars[offset]);
    r = dis(gen);
    param_assignment = param_assignment && (pars[offset] == r);
    cout << "Weight assigned: " << pars[offset] << "=" << r << "\n";
    offset++;
  }
  cout << "The network is: "
       << "\n"
       << nn << "\n";
  return nn && param_assignment;
}

Formula set_property(const vector<Variable>& outs) {
  Formula prop;
  for (const auto& o : outs) {
    prop = prop && o == 0.5;
  }
  cout << "Property: "
       << "\n"
       << prop << "\n";
  return prop;
}

// Formula assign_params(const vector<Variable>& pars, const int d, const int w)
// {
//   Formula params;
//   for (int i = 0; i < d; i++) {
//     for (int j = 0; j < w; j++) {
//       params = params && (pars[i * (w + 1) + j] == 0.1);
//     }
//   }
//   cout << "The following parameters were assigned: "
//        << "\n"
//        << params << "\n";
//   return params;
// }
