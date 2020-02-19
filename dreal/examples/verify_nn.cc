#include "dreal/api/api.h"

#include <assert.h>
#include <iostream>
#include <string>
#include <vector>
#include <cmath>
#include <numeric>
#include <random>

using namespace std;
using namespace dreal;

random_device rd;  //random seed
mt19937 gen(rd()); //random generator with rd()
uniform_real_distribution<> dis(-2.0, 2.0); //will turn gen into uniform distribution

Formula assign_bounds(const vector<Variable>& vars, const double lb, const double ub);//bounds in input variables
Formula generate_network(const vector<Variable>& vars, const vector<Variable>& pars, 
			const vector<Variable>& outs, const unsigned depth, const unsigned width);//generate network with random parameters
Formula set_property(const vector<Variable>&);//set requirements on the output here

int main() {
	const unsigned n=3; //number of input variables
	const unsigned m=1000; //number of parameters
	const unsigned k=2; //number of outputs
	const unsigned d=2; //depth
	const unsigned w=4; //width
	assert(d*w<m);
	vector<Variable> vars; //all vars
	vector<Variable> pars; //all parameters
	vector<Variable> outs; //all outputs
	//initialize the variables
	for (unsigned i=0; i<n; i++) {
		vars.push_back(Variable("x_"+to_string(i)));
	}
	for (unsigned i=0; i<m; i++) {
		pars.push_back(Variable("p_"+to_string(i)));
	}
	for (unsigned i=0; i<k; i++) {
		outs.push_back(Variable("y_"+to_string(i)));
	}		
	//configs for the solver
	Config config;
	config.mutable_precision() = 0.01;
	config.mutable_use_local_optimization() = true;
	//encode the network
	const Formula nn = generate_network(vars, pars, outs, d, w);
	//bounds on vars
	const Formula bounds = assign_bounds(vars, -2.0, 2.0);
	//property
	const Formula property = set_property(outs);
	//solve
	const auto result = CheckSatisfiability(bounds && nn && property, config);
	//output
	if (result) {
		cout <<endl<<"Result: Sat. The following assignment satisfies the conditions." << endl << *result << endl;
	} else {
		cout <<endl<<"Result: Unsat." << endl;
	}
}

Formula assign_bounds(const vector<Variable>& vars, const double lb, const double ub) {
	assert(lb<=ub);
	Formula bounds;
	for (auto& v: vars) {
		bounds = bounds && (v > lb) && (v < ub);
	}
	cout << "The following bounds were set: "<<endl<<bounds<<endl;
	return bounds;
}

Formula generate_network(const vector<Variable>& vars, const vector<Variable>& pars, 
		const vector<Variable>& outs, const unsigned depth, const unsigned width) {
	vector<Expression> layer_input;
	Formula param_assignment;
	double r;
	for (auto& v: vars) {
		layer_input.push_back(v);
		cout<<"Input variable: "<<v<<endl;
	}	
	unsigned offset = 0; //keep track of consumption of parameters
	for (unsigned i=0; i<depth; i++) {
		vector<Expression> layer_output;
		for (unsigned j=0; j<width; j++) {
			Expression single_output;
			for (unsigned k=0; k<layer_input.size(); k++) {
				single_output = single_output + layer_input[k]*pars[offset];
				r = dis(gen);
				param_assignment = param_assignment && (pars[offset]==r);//assign random value dis(gen)
				cout<<"Weight assigned: "<<pars[offset]<<"="<<r<<endl;
				offset++;
			}
			//layer_output.push_back(tanh(single_output+pars[offset]));
			layer_output.push_back(tanh(single_output+pars[offset]));
			r = dis(gen);
			param_assignment = param_assignment && (pars[offset]==r);
			cout<<"Weight assigned: "<<pars[offset]<<"="<<r<<endl;
			offset++;
		}
		layer_input = layer_output;
	}
	Formula nn;
	for (auto& o : outs) {
		Expression single_output;
		for (unsigned k=0; k<layer_input.size(); k++) {
			single_output = single_output + layer_input[k]*pars[offset];
			r = dis(gen);
			param_assignment = param_assignment && (pars[offset]==r);
			cout<<"Weight assigned: "<<pars[offset]<<"="<<r<<endl;
			offset++;
		}
		nn = nn && (o == single_output+pars[offset]);
		r = dis(gen);
		param_assignment = param_assignment && (pars[offset]==r);
		cout<<"Weight assigned: "<<pars[offset]<<"="<<r<<endl;
		offset++;
	}
	cout <<"The network is: "<<endl<<nn<<endl;
	return nn && param_assignment;
}

Formula set_property(const vector<Variable>& outs) {
	Formula prop;
	for (auto& o : outs) {
		prop = prop && o==0.5;
	}
	cout <<"Property: "<<endl<< prop<<endl;
	return prop;
}

/*
Formula assign_params(const vector<Variable>& pars, const unsigned d, const unsigned w) {
	Formula params;
	for (unsigned i=0; i<d; i++) {
		for (unsigned j=0; j<w; j++) {
			params = params && (pars[i*(w+1)+j]==0.1);
		}
	}
	cout << "The following parameters were assigned: " << endl << params << endl;
	return params;
}
*/





