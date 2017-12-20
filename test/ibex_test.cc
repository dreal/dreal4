//============================================================================
//                                  I B E X
// File        : ctc01.cpp
// Author      : Gilles Chabert
// Copyright   : Ecole des Mines de Nantes (France)
// License     : See the LICENSE file
// Created     : Jun 3, 2012
// Last Update : Jun 3, 2012
//============================================================================
#include "./ibex.h"

#include <cmath>
#include <iostream>

using std::cout;
using std::endl;
using std::sqrt;

int main() {
  {
    // Example #13
    // ------------------------------------------------
    // Contractor
    //
    // > Create the function (x,y)->( ||(x,y)||-d,  ||(x,y)-(1,1)||-d )
    // > Create the contractor "projection of f=0"
    //   (i.e., contraction of the input box w.r.t. f=0)
    // > Embed this contractor in a generic fix-point loop
    // ------------------------------------------------

    // We do the following to avoid memory leak. See
    // https://github.com/ibex-team/ibex-lib/issues/137#issuecomment-104536311
    const auto& x = ibex::ExprSymbol::new_();
    const auto& y = ibex::ExprSymbol::new_();
    const double d = 0.5 * sqrt(2);
    ibex::Function f(
        x, y,
        ibex::Return(ibex::sqrt(ibex::sqr(x) + ibex::sqr(y)) - d,
                     ibex::sqrt(ibex::sqr(x - 1.0) + ibex::sqr(y - 1.0)) - d));
    cout << f << endl;

    double init_box[][2] = {{-10, 10}, {-10, 10}};
    ibex::IntervalVector box(2, init_box);

    ibex::CtcFwdBwd c(f);
    c.contract(box);
    cout << "box after proj=" << box << endl;

    ibex::CtcFixPoint fp(c, 1e-03);

    fp.contract(box);
    cout << "box after fixpoint=" << box << endl;
  }

  {
    // Example #14
    // ------------------------------------------------
    // Combining FwdBwdection and Newton Contractor
    //
    // > Create the projection contractor on the same function
    //   as in the last example
    // > Contract the initial box x to x'
    // > Create the Newton iteration contractor
    // > Contract the box x'
    // ------------------------------------------------
    const auto& x = ibex::ExprSymbol::new_();
    const auto& y = ibex::ExprSymbol::new_();
    const double d = 1.0;
    ibex::Function f(x, y,
                     ibex::Return(sqrt(sqr(x) + sqr(y)) - d,
                                  sqrt(sqr(x - 1.0) + sqr(y - 1.0)) - d));
    cout << f << endl;

    double init_box[][2] = {{0.9, 1.1}, {-0.1, 0.1}};
    ibex::IntervalVector box(2, init_box);

    ibex::CtcFwdBwd c(f);
    c.contract(box);
    cout << "box after proj=" << box << endl;

    ibex::CtcNewton newton(f);
    newton.contract(box);
    cout << "box after newton=" << box << endl;
  }
}
