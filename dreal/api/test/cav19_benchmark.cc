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
// Artifact evaluation of the following paper:
//
// Sicun Gao, James Kapinski, Jyotirmoy Deshmukh, Nima Roohi, Armando
// Solar-Lezama, Nikos Arechiga and Soonho Kong, "Numerically-Robust
// Inductive Proof Rules for Continuous Dynamical Systems." In CAV
// (International Conference on Computer Aided Verification) 2019
//
// Author: Nima Roohi (http://cseweb.ucsd.edu/~nroohi/)

#include <chrono>
#include <iostream>
#include <sstream>
#include <vector>

#include "dreal/api/api.h"
#include "dreal/symbolic/symbolic.h"

namespace dreal {

using std::cout;
using std::endl;
using std::string;
using std::stringstream;

namespace {

int g_number_of_jobs = 1;

Expression operator^(Variable const& x, unsigned const n) { return pow(x, n); }

Expression sqr(Expression const& e) { return pow(e, 2); }

struct timer {
  timer() : point(std::chrono::high_resolution_clock::now()) {}
  auto milliseconds() {
    auto now = std::chrono::high_resolution_clock::now();
    auto old = point;
    point = now;
    return std::chrono::duration_cast<std::chrono::milliseconds>(now - old)
        .count();
  }
  std::chrono::time_point<std::chrono::high_resolution_clock> point;
};

// Check ε-Lyapunov stability.
void check_eps_Lyapunov_stability(double const alpha, double const beta,
                                  double const gamma, double const eps1,
                                  double const eps2, double const delta,
                                  Expression const& ball, Expression const& V,
                                  Expression const& lieV) {
  timer t;
  Config config;
  config.mutable_precision() = delta;
  config.mutable_number_of_jobs() = g_number_of_jobs;

  auto const cond1 = imply(eps2 * eps2 >= ball, V <= beta);
  auto const cond2 =
      imply(eps1 * eps1 <= ball && ball <= eps1 * eps1 * 1.001, V >= alpha);
  auto const cond3 =
      imply(eps2 * eps2 <= ball && ball <= eps1 * eps1, lieV <= -gamma);

  auto result = CheckSatisfiability(!cond1 || !cond2 || !cond3, config);

  if (result) {
    cout << "ERROR: Invalid Condition\n";
    return;
  }

  auto const total_time = t.milliseconds();
  cout << "epsilon-Stability is proved in " << total_time / 1000.0
       << " seconds,\n"
       << "\tepsilon : " << eps1 << "\n"
       << "\tepsilon': " << eps2 << "\n"
       << "\talpha   : " << alpha << "\n"
       << "\tbeta    : " << beta << "\n"
       << "\tgamma   : " << gamma << "\n"
       << "\tdelta   : " << config.precision() << "\n";
}

// Check Type-1 ε-barrier function.
void check_eps_barrier_type_1(double const eps, double const gamma,
                              double const delta, Expression const& level,
                              Formula const& level_ball, Formula const& ball,
                              Expression const& V, Expression const& lieV) {
  timer t;
  Config config;
  config.mutable_precision() = delta;
  config.mutable_number_of_jobs() = g_number_of_jobs;

  // We take `init` to be the set of values for which B(x)≤−ε hold. Therefore,
  // there is no need to prove that.
  auto const cond =
      imply(V - level == -eps && ball && level_ball, lieV <= -gamma);

  auto result = CheckSatisfiability(!cond, config);
  if (result) {
    cout << "ERROR: Invalid Condition\n";
    return;
  }

  auto const total_time = t.milliseconds();
  stringstream level_str;
  if (is_true(level_ball))
    level_str << level;
  else
    level_str << level_ball;
  cout << "Type 1 epsilon-barrier is proved in " << total_time / 1000.0
       << " seconds,\n"
       << "\tepsilon : " << eps << "\n"
       << "\tgamma   : " << gamma << "\n"
       << "\tlevel   : " << level_str.str() << "\n"
       << "\tdelta   : " << config.precision() << "\n";
}

// Time-Reversed Van der Pol.
struct reversed_time_van_der_pol {
  Variable const x1{"x1"};
  Variable const x2{"x2"};
  Expression const f1 = -x2;
  Expression const f2 = ((x1 ^ 2) - 1) * x2 + x1;
  Expression const V =
      42.419930460509669 * (x1 ^ 2) - 25.467284450100433 * x1 * x2 +
      29.037525088273682 * (x2 ^ 2) + 0.246437703822396 * (x1 ^ 3) +
      0.342787267928099 * (x1 ^ 2) * x2 + 0.070061019768681 * x1 * (x2 ^ 2) +
      0.056167250785361 * (x2 ^ 3) - 9.747135277935248 * (x1 ^ 4) +
      1.281447375757236 * (x1 ^ 3) * x2 -
      1.066167940090009 * (x1 ^ 2) * (x2 ^ 2) -
      0.111337393290709 * x1 * (x2 ^ 3) - 3.148132699966833 * (x2 ^ 4) -
      0.058675653184320 * (x1 ^ 5) - 0.088630122702897 * (x1 ^ 4) * x2 -
      0.035603912757564 * (x1 ^ 3) * (x2 ^ 2) -
      0.092730054611810 * (x1 ^ 2) * (x2 ^ 3) +
      0.030783940378564 * x1 * (x2 ^ 4) - 0.016849595361031 * (x2 ^ 5) +
      1.362207232588218 * (x1 ^ 6) + 1.257918398491556 * (x1 ^ 5) * x2 +
      0.407802497440289 * (x1 ^ 4) * (x2 ^ 2) -
      1.168667210949858 * (x1 ^ 3) * (x2 ^ 3) +
      1.839303562141088 * (x1 ^ 2) * (x2 ^ 4) -
      0.729105138802864 * x1 * (x2 ^ 5) + 0.326281890950742 * (x2 ^ 6);

  void epsilon_stability() const {
    Expression const ball = x1 * x1 + x2 * x2;
    Expression const lieV = f1 * V.Differentiate(x1) + f2 * V.Differentiate(x2);
    check_eps_Lyapunov_stability(2.1e-23, 1.7e-23, 1.00e-25, 1.00e-12, 5.00e-13,
                                 1e-25, ball, V, lieV);
  }

  void type1_barrier() const {
    auto const ball = -5 <= x1 && x1 <= 5 && -5 <= x2 && x2 <= 5;
    Expression const lieV = f1 * V.Differentiate(x1) + f2 * V.Differentiate(x2);
    check_eps_barrier_type_1(1e-5, 1e-5, 1e-4, 90, Formula::True(), ball, V,
                             lieV);
  }
};

// Normalized Pendulum.
struct normalized_pendulum {
  Variable const x1{"x1"};
  Variable const x2{"x2"};
  Expression const f1 = x2;
  Expression const f2 = -sin(x1) - x2;
  Expression const V = x2 * (24 * x1 + 92 * x2) + x1 * (100 * x1 + 24 * x2);

  void epsilon_stability() {
    Expression const ball = x1 * x1 + x2 * x2;
    Expression const lieV = f1 * V.Differentiate(x1) + f2 * V.Differentiate(x2);
    check_eps_Lyapunov_stability(7.07e-23, 3.97e-23, 1.00e-50, 1.00e-12,
                                 5.00e-13, 1e-50, ball, V, lieV);
  }

  void type1_barrier() {
    auto const b = 1000.0;
    auto const ball = -b <= x1 && x1 <= b && -b <= x2 && x2 <= b;
    Variable const level("level");
    auto const level_ball = 1.0 <= 10.0 * level && level <= 10;
    Expression const lieV = f1 * V.Differentiate(x1) + f2 * V.Differentiate(x2);
    check_eps_barrier_type_1(0.01, 0.01, 0.01, level, level_ball, ball, V,
                             lieV);
  }
};

// Moore-Greitzer Jet Engine
struct moore_jet_engine {
  Variable const x1{"x1"};
  Variable const x2{"x2"};
  Expression const f1 = -x2 - 1.5 * x1 * x1 - 0.5 * x1 * x1 * x1;
  Expression const f2 = 3 * x1 - x2;
  Expression const V =
      x2 * (31.294269 * x2 - 9.7437617 * x1 - 18.856765 * x1 * x2 +
            22.509931 * (x1 ^ 2) + 11.165278 * (x2 ^ 2)) -
      1.0 * x1 *
          (9.7437617 * x2 - 100.0 * x1 - 48.132286 * x1 * x2 +
           60.459815 * (x1 ^ 2) + 12.035111 * (x2 ^ 2)) +
      (x1 ^ 2) * (22.509931 * x2 - 60.459815 * x1 - 88.160775 * x1 * x2 +
                  100.0 * (x1 ^ 2) + 31.337433 * (x2 ^ 2)) +
      (x2 ^ 2) * (11.165278 * x2 - 12.035111 * x1 - 27.051686 * x1 * x2 +
                  31.337433 * (x1 ^ 2) + 14.189252 * (x2 ^ 2)) -
      1.0 * x1 * x2 *
          (18.856765 * x2 - 48.132286 * x1 - 81.481369 * x1 * x2 +
           88.160775 * (x1 ^ 2) + 27.051686 * (x2 ^ 2));

  void epsilon_stability() const {
    Expression const ball = x1 * x1 + x2 * x2;
    Expression const lieV = f1 * V.Differentiate(x1) + f2 * V.Differentiate(x2);
    check_eps_Lyapunov_stability(2.95e-19, 2.55e-19, 1.00e-20, 1.00e-10,
                                 5.00e-11, 1e-20, ball, V, lieV);
  }

  void type1_barrier() const {
    auto const b = 1000.0;
    auto const ball = -b <= x1 && x1 <= b && -b <= x2 && x2 <= b;
    Variable const level("level");
    auto const level_ball = 1 <= level && level <= 10;
    Expression const lieV = f1 * V.Differentiate(x1) + f2 * V.Differentiate(x2);
    check_eps_barrier_type_1(0.1, 0.1, 0.1, level, level_ball, ball, V, lieV);
  }
};

// Powertrain Control System
struct powertrain {
  Variable const x1{"x1"};
  Variable const x2{"x2"};
  Variable const x3{"x3"};
  Variable const x4{"x4"};

  Expression const dx1 =
      19.079360496000000441654265159741 *
          sqrt(x1 - 1.0 * sqr(x1 + 0.89877559179912203113360646966612) +
               0.89877559179912203113360646966612) -
      9.07480224 * x1 +
      2.7855072 * sqr(x1 + 0.89877559179912203113360646966612) -
      8.0049502737159982381646017302046;
  Expression const dx2 =
      (4.0 *
       (21.958 * x1 - 6.74 * sqr(x1 + 0.89877559179912203113360646966612) +
        19.369314444725121559631730860929)) /
          ((19.7622 * x3 - 6.066 * sqr(x3 + 1.0779564350547792273005143215414) +
            20.973390660839558045758224125166) *
           (0.4 * x2 + x4 + 1.0)) -
      4.0 * x2 - 4.0;
  Expression const dx3 =
      19.079360496000000441654265159741 *
          sqrt(x1 - 1.0 * sqr(x1 + 0.89877559179912203113360646966612) +
               0.89877559179912203113360646966612) -
      8.167322016 * x3 +
      2.50695648 * sqr(x3 + 1.0779564350547792273005143215414) -
      8.6678828923117725491509588664485;
  Expression const dx4 = 0.4 * x2;

  Expression const V =
      (x3 ^ 2) * (65.308154169384877718584903050214 * (x1 ^ 2) +
                  35.629697064563629282929468899965 * x1 * x2 +
                  44.069410977053095734845555853099 * x1 * x3 +
                  13.422472447088798830350242496934 * x1 * x4 +
                  64.300669960817359083193878177553 * x1 +
                  24.681043921437535004770325031132 * (x2 ^ 2) +
                  5.8501714294486406586770499416161 * x2 * x3 +
                  9.3542642172480157114478060975671 * x2 * x4 +
                  24.605677922649931588239269331098 * x2 +
                  65.290148894616848451732948888093 * (x3 ^ 2) -
                  3.8443744036635214555985839979257 * x3 * x4 -
                  14.783879703875173916571839072276 * x3 +
                  23.700397060799982540402197628282 * (x4 ^ 2) -
                  4.6020777211154868524545236141421 * x4) +
      x4 * (33.794793874119910981335124233738 * (x1 ^ 2) +
            19.984673460367915254209947306663 * x1 * x2 -
            20.3284210805566623037066165125 * x1 * x3 +
            9.3830786053208630193012140807696 * x1 * x4 +
            6.11954374520380461888180434471 * x1 -
            25.380657366895899684777759830467 * (x2 ^ 2) +
            10.506503318962931103897062712349 * x2 * x3 +
            61.587578965980618761477671796456 * x2 * x4 +
            62.203666682550370126136840553954 * x2 -
            4.6020777211154868524545236141421 * (x3 ^ 2) +
            74.746980573289761196065228432417 * x3 * x4 +
            8.9556111364585202494481563917361 * x3 +
            4.7901490992212716335529876232613 * (x4 ^ 2) +
            99.903784017029181541147409006953 * x4) +
      x1 * (56.034756698293598731197562301531 * (x1 ^ 2) +
            26.994410618741049745494819944724 * x1 * x2 +
            45.197727714444901891965855611488 * x1 * x3 +
            5.7961826848171549286803383438382 * x1 * x4 +
            99.934805708726017314802447799593 * x1 +
            52.428173056065766388655902119353 * (x2 ^ 2) +
            2.3827445615504583287247442058288 * x2 * x3 -
            5.9436158075507012910065895994194 * x2 * x4 +
            15.169943237837017591118637938052 * x2 +
            64.300669960817359083193878177553 * (x3 ^ 2) +
            1.586345806066036701054144941736 * x3 * x4 -
            51.184556276183933221091137966141 * x3 -
            20.716121236409712480508460430428 * (x4 ^ 2) +
            6.11954374520380461888180434471 * x4) +
      x2 * (55.016301753678554575799353187904 * (x1 ^ 2) +
            80.130353232930772833242372144014 * x1 * x2 -
            8.8235087637629270318484486779198 * x1 * x3 -
            31.158578487587604399777774233371 * x1 * x4 +
            15.169943237837017591118637938052 * x1 -
            56.413663390464861890905012842268 * (x2 ^ 2) +
            16.570833786969103584851836785674 * x2 * x3 +
            77.685403514909424416146066505462 * x2 * x4 +
            94.495991596541188073388184420764 * x2 +
            24.605677922649931588239269331098 * (x3 ^ 2) +
            74.520631587014975139027228578925 * x3 * x4 -
            3.2813146300532904930946642707568 * x3 +
            59.085490214630716820920497411862 * (x4 ^ 2) +
            62.203666682550370126136840553954 * x4) -
      1.0 * (x2 ^ 2) *
          (-5.8529222442170940610139950877056 * (x1 ^ 2) +
           55.879956909793804697983432561159 * x1 * x2 -
           51.546448030929660433230310445651 * x1 * x3 -
           60.181400171932871501212503062561 * x1 * x4 -
           52.428173056065766388655902119353 * x1 -
           98.845615003244787999392428901047 * (x2 ^ 2) +
           5.1979626525992150831712024228182 * x2 * x3 +
           63.207416997606891584382537985221 * x2 * x4 +
           56.413663390464861890905012842268 * x2 -
           24.681043921437535004770325031132 * (x3 ^ 2) +
           66.151439226550891703482193406671 * x3 * x4 +
           6.3226518377343507992804916284513 * x3 +
           60.444632688780593809951824368909 * (x4 ^ 2) +
           25.380657366895899684777759830467 * x4) +
      x3 * (13.574811110825400817248009843752 * (x1 ^ 2) -
            30.62989526579522703286784235388 * x1 * x2 +
            11.128565082439868305641539336648 * x1 * x3 +
            55.923242924611365367582038743421 * x1 * x4 -
            51.184556276183933221091137966141 * x1 -
            6.3226518377343507992804916284513 * (x2 ^ 2) +
            2.5305163782658994797714058222482 * x2 * x3 +
            9.5193750652277007162638255977072 * x2 * x4 -
            3.2813146300532904930946642707568 * x2 -
            14.783879703875173916571839072276 * (x3 ^ 2) -
            19.657147142343216472681888262741 * x3 * x4 +
            78.391449665619674647132342215627 * x3 +
            39.03958279098961980935200699605 * (x4 ^ 2) +
            8.9556111364585202494481563917361 * x4) +
      (x1 ^ 2) * (96.980461809678160989278694614768 * (x1 ^ 2) +
                  43.134658039978447163775854278356 * x1 * x2 +
                  44.026348911505223782114626374096 * x1 * x3 +
                  30.731198103536542021174682304263 * x1 * x4 +
                  56.034756698293598731197562301531 * x1 +
                  5.8529222442170940610139950877056 * (x2 ^ 2) +
                  9.7524369585081895905886995024048 * x2 * x3 +
                  42.412013164397912134973012143746 * x2 * x4 +
                  55.016301753678554575799353187904 * x2 +
                  65.308154169384877718584903050214 * (x3 ^ 2) +
                  23.745297723607126982869885978289 * x3 * x4 +
                  13.574811110825400817248009843752 * x3 +
                  51.196846029680216361157363280654 * (x4 ^ 2) +
                  33.794793874119910981335124233738 * x4) +
      (x4 ^ 2) * (51.196846029680216361157363280654 * (x1 ^ 2) +
                  57.978195050998152737520285882056 * x1 * x2 +
                  7.64181405257148860243887611432 * x1 * x3 -
                  8.5948600330515887435467448085546 * x1 * x4 -
                  20.716121236409712480508460430428 * x1 -
                  60.444632688780593809951824368909 * (x2 ^ 2) +
                  10.181765334712114423609818913974 * x2 * x3 +
                  59.349711728556528100853029172868 * x2 * x4 +
                  59.085490214630716820920497411862 * x2 +
                  23.700397060799982540402197628282 * (x3 ^ 2) +
                  28.294960436487258448323700577021 * x3 * x4 +
                  39.03958279098961980935200699605 * x3 +
                  99.245266674183056920810486190021 * (x4 ^ 2) +
                  4.7901490992212716335529876232613 * x4) +
      x2 * x3 *
          (9.7524369585081895905886995024048 * (x1 ^ 2) +
           13.255942820997219655509979929775 * x1 * x2 +
           1.4508389976544340260744547776994 * x1 * x3 -
           0.41660724878873112153598867735127 * x1 * x4 +
           2.3827445615504583287247442058288 * x1 -
           5.1979626525992150831712024228182 * (x2 ^ 2) +
           6.5496815974164581675154295226093 * x2 * x3 +
           12.412663135558824833992730418686 * x2 * x4 +
           16.570833786969103584851836785674 * x2 +
           5.8501714294486406586770499416161 * (x3 ^ 2) +
           8.3374379589262126444282330339774 * x3 * x4 +
           2.5305163782658994797714058222482 * x3 +
           10.181765334712114423609818913974 * (x4 ^ 2) +
           10.506503318962931103897062712349 * x4) +
      x3 * x4 *
          (23.745297723607126982869885978289 * (x1 ^ 2) +
           58.927922470796040954610361950472 * x1 * x2 -
           42.261711786337272656055574771017 * x1 * x3 -
           46.641804443188135564923868514597 * x1 * x4 +
           1.586345806066036701054144941736 * x1 -
           66.151439226550891703482193406671 * (x2 ^ 2) +
           8.3374379589262126444282330339774 * x2 * x3 +
           74.174652030905889432688127271831 * x2 * x4 +
           74.520631587014975139027228578925 * x2 -
           3.8443744036635214555985839979257 * (x3 ^ 2) +
           97.964663577133094918281130958349 * x3 * x4 -
           19.657147142343216472681888262741 * x3 +
           28.294960436487258448323700577021 * (x4 ^ 2) +
           74.746980573289761196065228432417 * x4) +
      x1 * x4 *
          (30.731198103536542021174682304263 * (x1 ^ 2) -
           59.13248982851327895104986964725 * x1 * x2 +
           44.877288818203986409116623690352 * x1 * x3 +
           97.179533978677156369485601317137 * x1 * x4 +
           5.7961826848171549286803383438382 * x1 +
           60.181400171932871501212503062561 * (x2 ^ 2) -
           0.41660724878873112153598867735127 * x2 * x3 -
           24.415489664611641273950226604939 * x2 * x4 -
           31.158578487587604399777774233371 * x2 +
           13.422472447088798830350242496934 * (x3 ^ 2) -
           46.641804443188135564923868514597 * x3 * x4 +
           55.923242924611365367582038743421 * x3 -
           8.5948600330515887435467448085546 * (x4 ^ 2) +
           9.3830786053208630193012140807696 * x4) +
      x1 * x3 *
          (44.026348911505223782114626374096 * (x1 ^ 2) -
           6.1452664233225160472784409648739 * x1 * x2 +
           59.950195047642424128753191325814 * x1 * x3 +
           44.877288818203986409116623690352 * x1 * x4 +
           45.197727714444901891965855611488 * x1 +
           51.546448030929660433230310445651 * (x2 ^ 2) +
           1.4508389976544340260744547776994 * x2 * x3 -
           19.41038686798670553912415925879 * x2 * x4 -
           8.8235087637629270318484486779198 * x2 +
           44.069410977053095734845555853099 * (x3 ^ 2) -
           42.261711786337272656055574771017 * x3 * x4 +
           11.128565082439868305641539336648 * x3 +
           7.64181405257148860243887611432 * (x4 ^ 2) -
           20.3284210805566623037066165125 * x4) +
      x1 * x2 *
          (43.134658039978447163775854278356 * (x1 ^ 2) +
           96.192864860088249656655534636229 * x1 * x2 -
           6.1452664233225160472784409648739 * x1 * x3 -
           59.13248982851327895104986964725 * x1 * x4 +
           26.994410618741049745494819944724 * x1 -
           55.879956909793804697983432561159 * (x2 ^ 2) +
           13.255942820997219655509979929775 * x2 * x3 +
           59.712277229080498841540247667581 * x2 * x4 +
           80.130353232930772833242372144014 * x2 +
           35.629697064563629282929468899965 * (x3 ^ 2) +
           58.927922470796040954610361950472 * x3 * x4 -
           30.62989526579522703286784235388 * x3 +
           57.978195050998152737520285882056 * (x4 ^ 2) +
           19.984673460367915254209947306663 * x4) +
      x2 * x4 *
          (42.412013164397912134973012143746 * (x1 ^ 2) +
           59.712277229080498841540247667581 * x1 * x2 -
           19.41038686798670553912415925879 * x1 * x3 -
           24.415489664611641273950226604939 * x1 * x4 -
           5.9436158075507012910065895994194 * x1 -
           63.207416997606891584382537985221 * (x2 ^ 2) +
           12.412663135558824833992730418686 * x2 * x3 +
           80.484806395217958652210654690862 * x2 * x4 +
           77.685403514909424416146066505462 * x2 +
           9.3542642172480157114478060975671 * (x3 ^ 2) +
           74.174652030905889432688127271831 * x3 * x4 +
           9.5193750652277007162638255977072 * x3 +
           59.349711728556528100853029172868 * (x4 ^ 2) +
           61.587578965980618761477671796456 * x4);

  void type1_barrier() const {
    auto const ball = -0.1 <= x1 && x1 <= 0.1 && -0.1 <= x2 && x2 <= 0.1 &&
                      -0.1 <= x3 && x3 <= 0.1 && -0.1 <= x4 && x4 <= 0.1;
    Expression const lieV =
        dx1 * V.Differentiate(x1) + dx2 * V.Differentiate(x2) +
        dx3 * V.Differentiate(x3) + dx4 * V.Differentiate(x4);
    check_eps_barrier_type_1(0.00001, 1e-5, 0.00001, 0.01, Formula::True(),
                             ball, V, lieV);
  }
};

void print_example_name(string const& name) {
  string const sep =
      "---------------------------------------------------------------------";

  auto len = sep.length() - name.length();
  stringstream buff;
  auto mid = len / 2;
  len -= mid;
  while (--mid) buff << "-";
  buff << " " << name << " ";
  while (--len) buff << "-";
  cout << "\n" << sep << "\n" << buff.str() << "\n" << sep << endl;
}

void DoMain() {
  print_example_name("T.R. Van der Pol");
  reversed_time_van_der_pol running_example{};
  running_example.epsilon_stability();
  running_example.type1_barrier();

  print_example_name("Norm. Pend.");
  normalized_pendulum pend{};
  pend.epsilon_stability();
  pend.type1_barrier();

  print_example_name("Moore-Greitzer");
  moore_jet_engine jet{};
  jet.epsilon_stability();
  jet.type1_barrier();

  print_example_name("Powertrain");
  powertrain ptc{};
  ptc.type1_barrier();
}

}  // namespace
}  // namespace dreal

int main(int argc, const char* argv[]) {
  if (argc == 2) {
    dreal::g_number_of_jobs = std::max(atoi(argv[1]), 1);
  }
  dreal::DoMain();
}
