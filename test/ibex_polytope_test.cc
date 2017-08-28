//============================================================================
//                                  I B E X
// File        : doc-contractor.cpp
// Author      : Gilles Chabert
// Copyright   : Ecole des Mines de Nantes (France)
// License     : See the LICENSE file
// Created     : Apr 25, 2014
// Last Update : Jun 03, 2014
//============================================================================
// #include "./ibex.h"

// // NOLINTNEXTLINE(build/namespaces)
// using namespace ibex;

// //! [ctc-polytope-2-C]
// /**
//  * My own linear relaxation of a system
//  */
// class MyLinearRelax : public LinearRelax {
//  public:
//   /**
//    * We actually only accept linear systems Ax<=b :)
//    */
//   MyLinearRelax(const Matrix& A, const Vector& b)
//       : LinearRelax(2, 2), A(A), b(b) {}

//   virtual int linearization(const IntervalVector& box,
//                             LinearSolver& lp_solver) {
//     for (int i = 0; i < A.nb_rows(); i++)
//       // add the constraint in the LP solver
//       lp_solver.addConstraint(A[i], LEQ, b[i]);

//     // we return the number of constraints
//     return A.nb_rows();
//   }

//   Matrix A;
//   Vector b;
// };
// //! [ctc-polytope-2-C]

// //! [ctc-propag-1-C]
// class Count : public CtcFwdBwd {
//  public:
//   static int count;

//   explicit Count(const NumConstraint& ctr) : CtcFwdBwd(ctr) {}

//   void contract(IntervalVector& box) {
//     CtcFwdBwd::contract(box);
//     count++;
//   }
// };

// int Count::count = 0;
// //! [ctc-propag-1-C]

// //! [ctc-input-output-C]
// class Count2 : public CtcFwdBwd {
//  public:
//   static int count;

//   explicit Count2(const NumConstraint& ctr) : CtcFwdBwd(ctr) {
//     // The input bitset should have been created
//     // by the constructor CtcFwdBwd
//     assert(input != nullptr);

//     // overwrite the input and output lists calculated
//     // by CtcFwdBwd by adding all the variables
//     for (int i = 0; i < nb_var; i++) {
//       input->add(i);
//       output->add(i);
//     }
//   }

//   // NOLINTNEXTLINE(runtime/references)
//   void contract(IntervalVector& box) {
//     CtcFwdBwd::contract(box);
//     count++;
//   }
// };

// int Count2::count = 0;
// //! [ctc-input-output-C]

// //! [ctc-input-output-2-C]
// class MyCtc : public Ctc {
//   MyCtc() : Ctc(100) {  // my contractor works on 100 variables
//     // create the input list with all the variables set by default
//     input = new BitSet(BitSet::all(100));
//     // remove all the odd variables
//     for (int i = 0; i < 100; i++)
//       if (i % 2 == 1) input->remove(i);

//     // create the output list with all the variables unset by default
//     output = new BitSet(BitSet::empty(100));
//     // add all the odd variables
//     for (int i = 0; i < 100; i++)
//       if (i % 2 == 1) output->add(i);
//   }

//   //! [ctc-input-output-2-C]
// };

// int main() {
//   {
//     //! [ctc-compo-1-C]

//     // Create the function corresponding to an
//     // hyperplane of angle alpha
//     Variable x, y, alpha;
//     Function f(x, y, alpha, cos(alpha) * x + sin(alpha) * y);

//     // Size of the polygon
//     int n = 7;

//     // Array to store constraints (for cleanup)
//     Array<NumConstraint> ctrs(2 * n);

//     // Arrays to store contractors
//     Array<Ctc> ctc_out(n), ctc_in(n);

//     for (int i = 0; i < n; i++) {
//       // create the constraints of the two half-spaces
//       // delimited by f(x,y,i*2pi/n)=0
//       // and store them in the array
//       ctrs.set_ref(2 * i, *new NumConstraint(
//                               x, y, f(x, y, i * 2 * Interval::PI / n) <= 1));
//       ctrs.set_ref(2 * i + 1, *new NumConstraint(
//                                   x, y, f(x, y, i * 2 * Interval::PI / n) >
//                                   1));

//       // create the contractors for these constraints
//       // and place them in the arrays
//       ctc_out.set_ref(i, *new CtcFwdBwd(ctrs[2 * i]));
//       ctc_in.set_ref(i, *new CtcFwdBwd(ctrs[2 * i + 1]));
//     }

//     // Composition of the "outer" contractors
//     CtcCompo ctc_polygon_out(ctc_out);
//     // Union of the "inner" contractors
//     CtcUnion ctc_polygon_in(ctc_in);
//     //! [ctc-compo-1-C]

//     SepCtcPair sep(ctc_polygon_in, ctc_polygon_out);
//     Set set(2);
//     sep.contract(set, 0.01);

//     //! [ctc-compo-2-C]
//     // ************ cleanup ***************
//     for (int i = 0; i < n; i++) {
//       delete &ctc_in[i];
//       delete &ctc_out[i];
//     }
//     for (int i = 0; i < 2 * n; i++) {
//       delete &ctrs[i];
//     }
//     //! [ctc-compo-2-C]
//   }

//   {
//     //! [ctc-propag-2-C]

//     // Load a system of constraints
//     System sys("test/DiscreteBoundary-0100.bch");

//     // The array of contractors we will use
//     Array<Ctc> ctc(sys.nb_ctr);

//     for (int i = 0; i < sys.nb_ctr; i++)
//       // Create contractors from constraints and store them in "ctc"
//       ctc.set_ref(i, *new Count(sys.ctrs[i]));
//     //! [ctc-propag-2-C]

//     //! [ctc-propag-3-C]
//     double prec = 1e-03;  // Precision upto which we calculate the fixpoint
//     //! [ctc-propag-3-C]

//     //! [ctc-propag-4-C]
//     // =============================== with simple fixpoint
//     // ==============================
//     Count::count = 0;  // initialize the counter

//     CtcCompo compo(ctc);           // make the composition of all contractors
//     CtcFixPoint fix(compo, prec);  // make the fixpoint

//     IntervalVector box =
//         sys.box;  // tested box (load domains written in the file)

//     fix.contract(box);

//     //! [ctc-propag-4-C]

//     //! [ctc-propag-5-C]
//     // ================================= with propagation
//     // =================================
//     Count::count = 0;  // initialize the counter

//     CtcPropag propag(ctc, prec);  // Propagation of all contractors

//     IntervalVector box2 =
//         sys.box;  // tested box (load domains written in the file)

//     propag.contract(box2);

//     //! [ctc-propag-5-C]
//   }

//   {
//     // Load a system of constraints
//     System sys("test/DiscreteBoundary-0100.bch");

//     // The array of contractors we will use
//     Array<Ctc> ctc(sys.nb_ctr);

//     for (int i = 0; i < sys.nb_ctr; i++)
//       // Create contractors from constraints and store them in "ctc"
//       ctc.set_ref(i, *new Count2(sys.ctrs[i]));
//     //! [ctc-propag-2-C]

//     //! [ctc-propag-3-C]
//     double prec = 1e-03;  // Precision upto which we calculate the fixpoint
//     //! [ctc-propag-3-C]

//     //! [ctc-propag-4-C]
//     // =============================== with simple fixpoint
//     // ==============================
//     Count2::count = 0;  // initialize the counter

//     CtcPropag propag(ctc, prec);  // Propagation of all contractors

//     IntervalVector box2 =
//         sys.box;  // tested box (load domains written in the file)

//     propag.contract(box2);
//   }

//   {
//     //! [ctc-hc4-C]

//     // Load a system of equations
//     System sys("test/DiscreteBoundary-0100.bch");
//     // Create the HC4 propagation loop with this system
//     CtcHC4 hc4(sys);

//     // Test the contraction
//     IntervalVector box(sys.box);
//     hc4.contract(box);

//     //! [ctc-hc4-C]
//   }

//   {
//     //! [ctc-inv-C]

//     // Build a contractor on R² wrt (x>=0 and y>=0).
//     Variable x, y;
//     Function gx(x, y, x);  // build (x,y)->x
//     Function gy(x, y, y);  // build (x,y)->y

//     NumConstraint geqx(gx, GEQ);  // build x>=0
//     NumConstraint geqy(gy, GEQ);  // build y>=0

//     CtcFwdBwd cx(geqx);
//     CtcFwdBwd cy(geqy);

//     CtcCompo compo(cx, cy);  // final contractor wrt (x>=0, y>=0)

//     // Build a mapping from R to R²
//     Variable t;
//     Array<const ExprNode> ret(2);
//     ret.set_ref(0, cos(t));
//     ret.set_ref(1, sin(t));
//     Function f(t, ExprVector::new_(ret, false));

//     // Build the inverse contractor
//     CtcInverse inv(compo, f);

//     double pi = 3.14;
//     IntervalVector box(1, Interval(0, 2 * pi));

//     inv.contract(box);

//     inv.contract(box);

//     //! [ctc-inv-C]
//   }

//   {
//     //! [ctc-polytope-1-C]

//     // build the matrix
//     double _A[4] = {1, 1, 1, -1};
//     Matrix A(2, 2, _A);

//     // build the vector
//     Vector b = Vector::zeros(2);

//     // create the linear system (with fixed matrix/vector)
//     LinearRelaxFixed lin(A, b);

//     // create the contractor w.r.t the linear system
//     CtcPolytopeHull ctc(lin);

//     // create a box
//     IntervalVector box(2, Interval(-1, 1));

//     // contract it
//     ctc.contract(box);

//     //! [ctc-polytope-1-C]
//   }

//   {
//     //! [ctc-exist-1-C]

//     // create a constraint on (x,y)
//     Variable x, y;
//     NumConstraint c(x, y, sqr(x) + sqr(y) <= 1);

//     // create domains for x and y
//     IntervalVector box_x(1, Interval(-10, 10));
//     IntervalVector box_y(1, Interval(-1, 1));

//     // set the precision that controls how much y will be bisected
//     double epsilon = 1.0;

//     // create a contractor on x by transforming y into an
//     // existentially-quantified parameter.
//     CtcExist exist_y(c, y, box_y, epsilon);

//     // contract the domain of x
//     exist_y.contract(box_x);

//     //! [ctc-exist-1-C]
//   }

//   {
//     //! [ctc-exist-2-C]

//     // create a conjunction of two constraint on (x,y)
//     Variable x, y;
//     Function f(x, y, Return(sqr(x) + sqr(2 * y - y), y - x));
//     IntervalVector z(2);
//     z[0] = Interval(0, 1);
//     z[1] = Interval::ZERO;
//     NumConstraint c(x, y, f(x, y) = z);

//     // create domains for y
//     IntervalVector box_y(1, Interval(-1, 1));

//     // observe the result of the contraction for
//     // different precision epsilon=10^{-_log}
//     for (int _log = 0; _log <= 8; _log++) {
//       // create the domain for x
//       IntervalVector box_x(1, Interval(-10, 10));

//       // create the exist-contractor with the new precision
//       CtcExist exist_y(c, y, box_y, ::pow(10, -_log));

//       // contract the box
//       exist_y.contract(box_x);
//     }
//     //! [ctc-exist-2-C]
//   }

//   {
//     //! [ctc-exist-3-C]

//     // create a system
//     Variable x, y;
//     SystemFactory fac;
//     fac.add_var(x);
//     fac.add_var(y);
//     fac.add_ctr(sqr(x) + sqr(2 * y - y) <= 1);
//     fac.add_ctr(x = y);

//     System sys(fac);

//     CtcHC4 hc4(sys);

//     // create domains for y
//     IntervalVector box_y(1, Interval(-1, 1));

//     // Creates the bitset structure that indicates which
//     // component are "quantified". The indices vary
//     // from 0 to 1 (2 variables only). These are the
//     // two first arguments. The bitset is initially empty
//     // which means that, by default, all the variables
//     // are parameters.
//     BitSet vars(0, 1, BitSet::empt);

//     // Add "x" as variable.
//     vars.add(0);

//     // observe the result of the contraction for
//     // different precision epsilon=10^{-_log}
//     for (int _log = 0; _log <= 8; _log++) {
//       // create the domain for x
//       IntervalVector box_x(1, Interval(-10, 10));

//       // create the exist-contractor with the new precision
//       CtcExist exist_y(hc4, vars, box_y, ::pow(10, -_log));

//       // contract the box
//       exist_y.contract(box_x);
//     }
//     //! [ctc-exist-3-C]
//   }
// }

int main() {}
