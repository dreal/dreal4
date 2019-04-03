%{

#include <cmath>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <string>
#include <tuple>
#include <utility>

#include "dreal/smt2/logic.h"
#include "dreal/smt2/sort.h"
#include "dreal/smt2/term.h"
#include "dreal/symbolic/symbolic.h"
#include "dreal/util/math.h"

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wold-style-cast"
#pragma GCC diagnostic ignored "-Wdeprecated"

/* void yyerror(SmtPrsr parser, const char *); */
#define YYMAXDEPTH 1024 * 1024
%}

/*** yacc/bison Declarations ***/

/* Require bison 2.3 or later */
%require "2.3"

/* add debug output code to generated parser. disable this for release
 * versions. */
%debug

/* start symbol is named "script" */
%start script

/* write out a header file containing the token defines */
%defines

/* /\* use newer C++ skeleton file *\/ */
%skeleton "lalr1.cc"

/* namespace to enclose parser in */
%define api.prefix {dreal}

/* set the parser's class identifier */
%define parser_class_name {Smt2Parser}

/* keep track of the current position within the input */
%locations
%initial-action
{
    // initialize the initial location object
    @$.begin.filename = @$.end.filename = &driver.streamname_;
};

/* The driver is passed by reference to the parser and to the scanner. This
 * provides a simple but effective pure interface, not relying on global
 * variables. */
%parse-param { class Smt2Driver& driver }

/* verbose error messages */
%define parse.error verbose


%union
{
    dreal::Sort               sortVal;
    std::int64_t              int64Val;
    std::string*              doubleVal;
    double                    hexfloatVal;
    std::string*              stringVal;
    Term*                     termVal;
    std::vector<Term>*        termListVal;
    std::tuple<Variable, double, double>* forallVariableVal;
    std::pair<Variables, Formula>*        forallVariablesVal;
    std::pair<std::string, Term>*              letBindVal;
    std::vector<std::pair<std::string, Term>>* letBindsVal;
}

%token TK_EXCLAMATION TK_BINARY TK_DECIMAL TK_HEXADECIMAL TK_NUMERAL TK_STRING
%token TK_UNDERSCORE TK_AS TK_EXISTS TK_FORALL TK_LET TK_PAR
%token TK_ASSERT TK_CHECK_SAT TK_CHECK_SAT_ASSUMING TK_DECLARE_CONST
%token TK_DECLARE_FUN TK_DECLARE_SORT TK_DEFINE_FUN TK_DEFINE_FUN_REC
%token TK_DEFINE_SORT TK_ECHO TK_EXIT TK_GET_ASSERTIONS TK_GET_ASSIGNMENT
%token TK_GET_INFO TK_GET_MODEL TK_GET_OPTION TK_GET_PROOF
%token TK_GET_UNSAT_ASSUMPTIONS TK_GET_UNSAT_CORE TK_GET_VALUE
%token TK_POP TK_PUSH TK_RESET TK_RESET_ASSERTIONS TK_SET_INFO
%token TK_SET_LOGIC TK_SET_OPTION

%token TK_PLUS TK_MINUS TK_TIMES TK_DIV
%token TK_EQ TK_LTE TK_GTE TK_LT TK_GT
%token TK_EXP TK_LOG TK_ABS TK_SIN TK_COS TK_TAN TK_ASIN TK_ACOS TK_ATAN TK_ATAN2
%token TK_SINH TK_COSH TK_TANH TK_MIN TK_MAX TK_SQRT TK_POW
%token TK_TRUE TK_FALSE TK_AND TK_OR TK_IMPLIES TK_NOT TK_ITE

%token TK_MAXIMIZE TK_MINIMIZE

%token                 END          0        "end of file"
%token <doubleVal>     DOUBLE                "double"
%token <hexfloatVal>   HEXFLOAT              "hexfloat"
%token <int64Val>      INT                   "int64"
%token <stringVal>     SYMBOL                "symbol"
%token <stringVal>     KEYWORD               "keyword"
%token <stringVal>     STRING                "string"

%type <sortVal>        sort
%type <termVal>        term
%type <termListVal>    term_list

%type <forallVariablesVal>   variable_sort_list
%type <forallVariableVal>    variable_sort
%type <letBindsVal>   var_binding_list
%type <letBindVal>    var_binding
                        
%{

#include "dreal/smt2/driver.h"
#include "dreal/smt2/scanner.h"

/* this "connects" the bison parser in the driver to the flex scanner class
 * object. it defines the yylex() function call to pull the next token from the
 * current lexer object of the driver context. */
#undef yylex
#define yylex driver.scanner_->lex

%}

%% /*** Grammar Rules ***/

script:         command_list END
                ;

command_list:   command
        |       command command_list
                ;

command:
                command_assert
        |       command_check_sat
        |       command_declare_fun
        |       command_exit
        |       command_get_model
        |       command_maximize
        |       command_minimize
        |       command_pop
        |       command_push
        |       command_set_info
        |       command_set_logic
        |       command_set_option
        ;

command_assert: '('TK_ASSERT term ')' {
                    driver.context_.Assert($3->formula());
                    delete $3;
                }
                ;
command_check_sat:
                '('TK_CHECK_SAT ')' {
                    driver.CheckSat();
                }
                ;
command_declare_fun:
                '(' TK_DECLARE_FUN SYMBOL '(' ')' sort ')' {
                    driver.DeclareVariable(*$3, $6);
                    delete $3;
                }
        |
                '(' TK_DECLARE_FUN SYMBOL '(' ')' sort '[' term ',' term ']' ')' {
                    driver.DeclareVariable(*$3, $6, *$8, *$10);
                    delete $3;
                    delete $8;
                    delete $10;
                }
        |
                '(' TK_DECLARE_CONST SYMBOL sort ')' {
                    driver.DeclareVariable(*$3, $4);
                    delete $3;
                }
        |
                '(' TK_DECLARE_CONST SYMBOL sort '[' term ',' term ']' ')' {
                    driver.DeclareVariable(*$3, $4, *$6, *$8);
                    delete $3;
                    delete $6;
                    delete $8;
                }
                ;

command_exit:   '('TK_EXIT ')' {
                    driver.context_.Exit();
                }
                ;

command_get_model:
                '('TK_GET_MODEL ')' {
                    driver.GetModel();
                }
                ;

command_maximize: '(' TK_MAXIMIZE term ')' {
                      driver.context_.Maximize($3->expression());
                      delete $3;
                }
                ;

command_minimize: '(' TK_MINIMIZE term ')' {
                      driver.context_.Minimize($3->expression());
                      delete $3;
                }
                ;

command_set_info:
                '(' TK_SET_INFO KEYWORD SYMBOL ')' {
                    driver
                        .context_
                        .SetInfo(*$3, *$4);
                    delete $3;
                    delete $4;
                }
        |       '(' TK_SET_INFO KEYWORD STRING ')' {
                    driver
                        .context_
                        .SetInfo(*$3, *$4);
                    delete $3;
                    delete $4;
                }
        |       '(' TK_SET_INFO KEYWORD DOUBLE ')' {
                    driver
                        .context_
                        .SetInfo(*$3, std::stod(*$4));
                    delete $3; delete $4;
                }
                ;
command_set_logic:
                '(' TK_SET_LOGIC SYMBOL ')' {
                    driver
                        .context_
                        .SetLogic(dreal::parse_logic(*$3));
                    delete $3;
                }
                ;
command_set_option:
                '(' TK_SET_OPTION KEYWORD SYMBOL ')' {
                    driver
                        .context_
                        .SetOption(*$3, *$4);
                    delete $3;
                    delete $4;
                }
        |       '('TK_SET_OPTION KEYWORD DOUBLE ')' {
                    driver
                        .context_
                        .SetOption(*$3, std::stod(*$4));
                    delete $3; delete $4;
                }
        |       '('TK_SET_OPTION KEYWORD TK_TRUE ')' {
                    driver
                        .context_
                        .SetOption(*$3, "true");
                    delete $3;
                }
        |       '('TK_SET_OPTION KEYWORD TK_FALSE ')' {
                    driver
                        .context_
                        .SetOption(*$3, "false");
                    delete $3;
                }

                ;

command_push:   '(' TK_PUSH INT ')' {
                    driver.context_.Push(convert_int64_to_int($3));
                }
                ;

command_pop:    '(' TK_POP INT ')' {
                    driver.context_.Pop(convert_int64_to_int($3));
                }
                ;

term_list:      term { $$ = new std::vector<Term>(1, *$1); delete $1; }
        |       term_list term { $1->push_back(*$2); $$ = $1; delete $2; }
        ;

term:           TK_TRUE { $$ = new Term(Formula::True()); }
        |       TK_FALSE { $$ = new Term(Formula::False()); }
        |       '('TK_EQ term term ')' {
            const Term& t1 = *$3;
            const Term& t2 = *$4;
            if (t1.type() == Term::Type::EXPRESSION &&
                t2.type() == Term::Type::EXPRESSION) {
                $$ = new Term(t1.expression() == t2.expression());
            } else if (t1.type() == Term::Type::FORMULA &&
                       t2.type() == Term::Type::FORMULA) {
                //    (f1 = f2)
                // -> (f1 ⇔ f2)
                // -> (f1 ∧ f2) ∨ (¬f1 ∧ ¬f2)
                $$ = new Term(t1.formula() == t2.formula());
            } else {
                std::cerr << @1 << " : Type mismatch in `t1 == t2`:" << std::endl
                          << "    t1 = " << t1 << std::endl
                          << "    t2 = " << t2 << std::endl;
                delete $3; delete $4;
                YYABORT;
            }
            delete $3; delete $4;
        }
        |       '('TK_LT term term ')' { $$ = new Term($3->expression() < $4->expression()); delete $3; delete $4; }
        |       '('TK_LTE term term ')' { $$ = new Term($3->expression() <= $4->expression()); delete $3; delete $4; }
        |       '('TK_GT term term ')' { $$ = new Term($3->expression() > $4->expression()); delete $3; delete $4; }
        |       '('TK_GTE term term ')' { $$ = new Term($3->expression() >= $4->expression()); delete $3; delete $4; }
        |       '('TK_AND term_list ')' {
            Formula f = Formula::True();
            for (const Term& t : *$3) {
                f = f && t.formula();
            }
            $$ = new Term(f);
            delete $3;
        }
        |       '('TK_OR term_list ')' {
            Formula f = Formula::False();
            for (const Term& t : *$3) {
                f = f || t.formula();
            }
            $$ = new Term(f);
            delete $3;
        }
        |       '('TK_NOT term ')' {
            $$ = new Term(!($3->formula()));
            delete $3;
        }
        |       '('TK_IMPLIES term term')' {
            $$ = new Term(!($3->formula()) || $4->formula());
            delete $3;
            delete $4;
        }
        |       '('TK_ITE term term term ')' {
            const Formula& cond = $3->formula();
            const Term& then_term = *$4;
            const Term& else_term = *$5;
            if (then_term.type() == Term::Type::EXPRESSION &&
                else_term.type() == Term::Type::EXPRESSION) {
                const Expression& e1 = then_term.expression();
                const Expression& e2 = else_term.expression();
                $$ = new Term{if_then_else(cond, e1, e2)};
            } else if (then_term.type() == Term::Type::FORMULA &&
                       else_term.type() == Term::Type::FORMULA) {
                //    if(cond) then f1 else f2
                // -> (cond => f1) ∧ (¬cond => f2)
                // -> (¬cond ∨ f1) ∧ (cond ∨ f2)
                const Formula& f1 = then_term.formula();
                const Formula& f2 = else_term.formula();
                $$ = new Term((!cond || f1) && (cond || f2));
            } else {
                std::cerr << @1 << " : Type mismatch in `if (c) then t1 else t2`:" << std::endl
                          << "    t1 = " << then_term << std::endl
                          << "    t2 = " << else_term << std::endl;
                delete $3; delete $4; delete $5;
                YYABORT;
            }
            delete $3; delete $4; delete $5;
        }
        |       '(' TK_FORALL enter_scope '(' variable_sort_list ')' term exit_scope ')' {
            const Variables& vars = $5->first;
            const Formula& domain = $5->second;
            $$ = new Term(forall(vars, imply(domain, $7->formula())));
            delete $5; delete $7;
        }
        |       '(' TK_LET enter_scope let_binding_list term exit_scope ')' {
            $$ = $5;
        }
        |       DOUBLE {
            const Box::Interval i{StringToInterval(*$1)};
            const double parsed{std::stod(*$1)};
            delete $1;
            if (i.diam() == 0) {
                // point => floating-point constant expression.
                $$ = new Term{i.mid()};
            } else {
                // interval => real constant expression.
                $$ = new Term{real_constant(i.lb(), i.ub(), i.lb() == parsed)};
            }
        }
        |       HEXFLOAT { $$ = new Term{$1}; }
        |       INT { $$ = new Term{convert_int64_to_double($1)}; }
        |       SYMBOL {
            try {
                const Variable& var = driver.lookup_variable(*$1);
                if (var.get_type() == Variable::Type::BOOLEAN) {
                    $$ = new Term(Formula(var));
                } else {
                    $$ = new Term(Expression(var));
                }
            } catch (std::runtime_error& e) {
                std::cerr << @1 << " : " << e.what() << std::endl;
                delete $1;              
                YYABORT;
            }
            delete $1;          
        }
        |       '(' TK_PLUS term ')' {
            $$ = $3;
        }
        |       '(' TK_PLUS term term_list ')' {
            for (const Term& term : *$4) {
                $3->mutable_expression() += term.expression();
            }
            $$ = $3;
            delete $4;
        }
        |       '(' TK_MINUS term ')' {
            $$ = new Term{- $3->expression()};
            delete $3;
        }
        |       '(' TK_MINUS term term_list ')' {
            for (const Term& term : *$4) {
                $3->mutable_expression() -= term.expression();
            }
            $$ = $3;
            delete $4;
        }
        |       '(' TK_TIMES term term_list ')' {
            for (const Term& term : *$4) {
                $3->mutable_expression() *= term.expression();
            }
            $$ = $3;
            delete $4;
        }
        |       '(' TK_DIV term term_list ')' {
            for (const Term& term : *$4) {
                $3->mutable_expression() /= term.expression();
            }
            $$ = $3;
            delete $4;
        }
        |       '('TK_EXP term ')' {
            $$ = new Term{exp($3->expression())};
            delete $3;
        }
        |       '('TK_LOG term ')' {
            $$ = new Term{log($3->expression())};
            delete $3;
        }
        |       '('TK_ABS term ')' {
            $$ = new Term{abs($3->expression())};
            delete $3;
        }
        |       '('TK_SIN term ')' {
            $$ = new Term{sin($3->expression())};
            delete $3;
            }
        |       '('TK_COS term ')' {
            $$ = new Term{cos($3->expression())};
            delete $3;
            }
        |       '('TK_TAN term ')' {
            $$ = new Term{tan($3->expression())};
            delete $3;
            }
        |       '('TK_ASIN term ')' {
            $$ = new Term{asin($3->expression())};
            delete $3;
            }
        |       '('TK_ACOS term ')' {
            $$ = new Term{acos($3->expression())};
            delete $3;
            }
        |       '('TK_ATAN term ')' {
            $$ = new Term{atan($3->expression())};
            delete $3;
            }
        |       '('TK_ATAN2 term term ')' {
            $$ = new Term{atan2($3->expression(), $4->expression())};
            delete $3;
            delete $4;
            }
        |       '('TK_SINH term ')' {
            $$ = new Term{sinh($3->expression())};
            delete $3;
            }
        |       '('TK_COSH term ')' {
            $$ = new Term{cosh($3->expression())};
            delete $3;
            }
        |       '('TK_TANH term ')' {
            $$ = new Term{tanh($3->expression())};
            delete $3;
            }
        |       '('TK_MIN term term ')' {
            $$ = new Term{min($3->expression(), $4->expression())};
            delete $3;
            delete $4;
            }
        |       '('TK_MAX term term ')' {
            $$ = new Term{max($3->expression(), $4->expression())};
            delete $3;
            delete $4;
            }
        |       '('TK_SQRT term ')' {
            $$ = new Term{sqrt($3->expression())};
            delete $3;
            }
        |       '('TK_POW term term ')' {
            $$ = new Term{pow($3->expression(), $4->expression())};
            delete $3;
            delete $4;
            }
        ;

let_binding_list: '(' var_binding_list ')' {
            // Locals must be bound simultaneously.
            for (auto& binding : *$2) {
                const std::string& name{ binding.first };
                const Term& term{ binding.second };
                const bool is_formula = term.type() == Term::Type::FORMULA;
                const Sort sort = is_formula ? Sort::Bool : Sort::Real;
                const Variable v{ driver.DeclareLocalVariable(name, sort) };
                if (is_formula) {
                    const Formula fv{v};
                    const Formula& ft{ term.formula() };
                    driver.context_.Assert((fv && ft) || (!fv && !ft));
                } else {
                    driver.context_.Assert(Expression{v} == term.expression());
                }
            }
            delete $2;
        }
        ;

enter_scope: /* */ {
            driver.PushScope();
        }
        ;

exit_scope: /* */ {
            driver.PopScope();
        }
        ;

variable_sort_list: /* empty list */ { $$ = new std::pair<Variables, Formula>(Variables{}, Formula::True()); }
        |       variable_sort variable_sort_list {
            const Variable& v = std::get<0>(*$1);
            const double lb = std::get<1>(*$1);
            const double ub = std::get<2>(*$1);
            $2->first.insert(v);
            if (std::isfinite(lb)) {
                $2->second = $2->second && (lb <= v);
            }
            if (std::isfinite(ub)) {
                $2->second = $2->second && (v <= ub);
            }
            delete $1; $$ = $2;
        }
        ;

variable_sort: '(' SYMBOL sort ')' {
            const Variable v = driver.RegisterVariable(*$2, $3);
            const double inf = std::numeric_limits<double>::infinity();
            $$ = new std::tuple<Variable, double, double>(v, -inf, inf);
            delete $2;
        }
        |       '(' SYMBOL sort '[' term ',' term ']' ')' {
            const Variable v = driver.RegisterVariable(*$2, $3);
            const double lb = $5->expression().Evaluate();
            const double ub = $7->expression().Evaluate();
            $$ = new std::tuple<Variable, double, double>(v, lb, ub);
            delete $2;
            delete $5;
            delete $7;
        }
        ;

sort:           SYMBOL { $$ = ParseSort(*$1); delete $1; }
                ;

var_binding_list: /* empty list */ {
            $$ = new std::vector<std::pair<std::string, Term>>;
        }
        | var_binding var_binding_list {
            $2->push_back(*$1);
            $$ = $2;
            delete $1;
        }
        ;

var_binding: '(' SYMBOL term ')' {
            $$ = new std::pair<std::string, Term>(*$2, *$3);
            delete $2;
            delete $3;
        }
        ;


%% /*** Additional Code ***/
void dreal::Smt2Parser::error(const Smt2Parser::location_type& l,
                              const std::string& m) {
    driver.error(l, m);
}

#pragma GCC diagnostic pop
