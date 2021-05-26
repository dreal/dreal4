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

#ifdef __clang__
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wunknown-warning-option"
#pragma clang diagnostic ignored "-Wdtor-name"
#endif

/* void yyerror(SmtPrsr parser, const char *); */
#define YYMAXDEPTH 1024 * 1024
%}

/*** yacc/bison Declarations ***/

/* Require bison 3.0.4 or later */
%require "3.0.4"

%define parse.trace

/* start symbol is named "script" */
%start script

/* write out a header file containing the token defines */
%defines

%language "c++"

/* namespace to enclose parser in */
%define api.prefix {dreal}

/* set the parser's class identifier */
%define parser_class_name {Smt2Parser}

/* keep track of the current position within the input */
%locations
%initial-action
{
    // initialize the initial location object
    @$.begin.filename = @$.end.filename = &driver.mutable_streamname();
};

/* The driver is passed by reference to the parser and to the scanner. This
 * provides a simple but effective pure interface, not relying on global
 * variables. */
%parse-param { class Smt2Driver& driver }

/* verbose error messages */
%define parse.error verbose

%define api.value.type variant

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
%token TK_TRUE TK_FALSE TK_AND TK_OR TK_XOR TK_IMPLIES TK_NOT TK_ITE

%token TK_MAXIMIZE TK_MINIMIZE

%token                   END          0        "end of file"
%token <std::string>     DOUBLE                "double"
%token <double>          HEXFLOAT              "hexfloat"
%token <std::int64_t>    INT                   "int64"
%token <std::string>     SYMBOL                "symbol"
%token <std::string>     KEYWORD               "keyword"
%token <std::string>     STRING                "string"

%type <dreal::Sort>       sort
%type <Term>              term
%type <std::vector<Term>> term_list

%type <std::tuple<Variable, double, double>>      variable_sort
%type <std::pair<Variables, Formula>>             variable_sort_list
%type <std::vector<std::pair<std::string, Term>>> var_binding_list
%type <std::pair<std::string, Term>>              var_binding

%type <Variable>              name_sort
%type <std::vector<Variable>> name_sort_list

%{

#include "dreal/smt2/driver.h"
#include "dreal/smt2/scanner.h"

/* this "connects" the bison parser in the driver to the flex scanner class
 * object. it defines the yylex() function call to pull the next token from the
 * current lexer object of the driver context. */
#undef yylex
#define yylex driver.scanner->lex

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
        |       command_define_fun
        |       command_exit
        |       command_get_model
        |       command_get_value
        |       command_maximize
        |       command_minimize
        |       command_pop
        |       command_push
        |       command_set_info
        |       command_set_logic
        |       command_set_option
        |       command_get_option
        ;

command_assert: '('TK_ASSERT term ')' {
                    driver.mutable_context().Assert($3.formula());
                }
                ;
command_check_sat:
                '('TK_CHECK_SAT ')' {
                    driver.CheckSat();
                }
                ;
command_declare_fun:
                '(' TK_DECLARE_FUN SYMBOL '(' ')' sort ')' {
                    driver.DeclareVariable($3, $6);
                }
        |
                '(' TK_DECLARE_FUN SYMBOL '(' ')' sort '[' term ',' term ']' ')' {
                    driver.DeclareVariable($3, $6, $8, $10);
                }
        |
                '(' TK_DECLARE_CONST SYMBOL sort ')' {
                    driver.DeclareVariable($3, $4);
                }
        |
                '(' TK_DECLARE_CONST SYMBOL sort '[' term ',' term ']' ')' {
                    driver.DeclareVariable($3, $4, $6, $8);
                }
        ;

command_define_fun:
                '(' TK_DEFINE_FUN SYMBOL enter_scope '(' name_sort_list ')' sort term exit_scope ')' {
                    if ($6.empty()) {
                        // No parameters - treat as variable, just like declare-fun.
                        const Variable v{driver.DeclareVariable($3, $8)};
                        if ($9.type() == Term::Type::FORMULA) {
                            driver.mutable_context().Assert(v == $9.formula());
                        } else {
                            driver.mutable_context().Assert(v == $9.expression());
                        }
                    } else {
                        driver.DefineFun($3, $6, $8, $9);
                    }
                }
                ;

command_exit:   '('TK_EXIT ')' {
                    driver.mutable_context().Exit();
		    YYACCEPT;
                }
                ;

command_get_model:
                '('TK_GET_MODEL ')' {
                    driver.GetModel();
                }
                ;

command_get_value:
                '(' TK_GET_VALUE '(' term_list ')' ')' {
                    driver.GetValue($4);
                }
                ;

command_maximize: '(' TK_MAXIMIZE term ')' {
                      driver.mutable_context().Maximize($3.expression());
                }
                ;

command_minimize: '(' TK_MINIMIZE term ')' {
                      driver.mutable_context().Minimize($3.expression());
                }
                ;

command_set_info:
                '(' TK_SET_INFO KEYWORD SYMBOL ')' {
                    driver
                        .mutable_context()
                        .SetInfo($3, $4);
                }
        |       '(' TK_SET_INFO KEYWORD STRING ')' {
                    driver
                        .mutable_context()
                        .SetInfo($3, $4);
                }
        |       '(' TK_SET_INFO KEYWORD DOUBLE ')' {
                    driver
                        .mutable_context()
                        .SetInfo($3, std::stod($4));
                }
                ;
command_set_logic:
                '(' TK_SET_LOGIC SYMBOL ')' {
                    driver
                        .mutable_context()
                        .SetLogic(dreal::parse_logic($3));
                }
                ;
command_set_option:
                '(' TK_SET_OPTION KEYWORD SYMBOL ')' {
                    driver
                        .mutable_context()
                        .SetOption($3, $4);
                }
        |       '('TK_SET_OPTION KEYWORD DOUBLE ')' {
                    driver
                        .mutable_context()
                        .SetOption($3, std::stod($4));
                }
        |       '('TK_SET_OPTION KEYWORD TK_TRUE ')' {
                    driver
                        .mutable_context()
                        .SetOption($3, "true");
                }
        |       '('TK_SET_OPTION KEYWORD TK_FALSE ')' {
                    driver
                        .mutable_context()
                        .SetOption($3, "false");
                }
                ;

command_get_option:
                '(' TK_GET_OPTION KEYWORD ')' {
                    driver
                        .GetOption($3);
                }
                ;


command_push:   '(' TK_PUSH INT ')' {
                    driver.mutable_context().Push(convert_int64_to_int($3));
                }
                ;

command_pop:    '(' TK_POP INT ')' {
                    driver.mutable_context().Pop(convert_int64_to_int($3));
                }
                ;

term_list:      term { $$ = std::vector<Term>(1, $1); }
        |       term_list term { $1.push_back($2); $$ = $1;  }
        ;

term:           TK_TRUE { $$ = Formula::True(); }
        |       TK_FALSE { $$ = Formula::False(); }
        |       '('TK_EQ term term ')' {
            const Term& t1 = $3;
            const Term& t2 = $4;
            if (t1.type() == Term::Type::EXPRESSION &&
                t2.type() == Term::Type::EXPRESSION) {
                $$ = t1.expression() == t2.expression();
            } else if (t1.type() == Term::Type::FORMULA &&
                       t2.type() == Term::Type::FORMULA) {
                //    (f1 = f2)
                // -> (f1 ⇔ f2)
                // -> (f1 ∧ f2) ∨ (¬f1 ∧ ¬f2)
                $$ = t1.formula() == t2.formula();
            } else {
                std::cerr << @1 << " : Type mismatch in `t1 == t2`:" << std::endl
                          << "    t1 = " << t1 << std::endl
                          << "    t2 = " << t2 << std::endl;
                YYABORT;
            }
        }
        |       '('TK_LT term term ')'  { $$ = $3.expression() <  $4.expression(); }
        |       '('TK_LTE term term ')' { $$ = $3.expression() <= $4.expression(); }
        |       '('TK_GT term term ')'  { $$ = $3.expression() >  $4.expression(); }
        |       '('TK_GTE term term ')' { $$ = $3.expression() >= $4.expression(); }
        |       '('TK_AND term_list ')' {
            Formula f = Formula::True();
            for (const Term& t : $3) {
                f = f && t.formula();
            }
            $$ = f;
        }
        |       '('TK_OR term_list ')' {
            Formula f = Formula::False();
            for (const Term& t : $3) {
                f = f || t.formula();
            }
            $$ = f;
        }
        |       '('TK_XOR term_list ')' {
            Formula f = Formula::False();
            for (const Term& t : $3) {
                f = (f && !t.formula()) || (!f && t.formula());
            }
            $$ = f;
        }
        |       '('TK_NOT term ')' {
            $$ = !($3.formula());
        }
        |       '('TK_IMPLIES term term')' {
            $$ = !($3.formula()) || $4.formula();
        }
        |       '('TK_ITE term term term ')' {
            const Formula& cond = $3.formula();
            const Term& then_term = $4;
            const Term& else_term = $5;
            if (then_term.type() == Term::Type::EXPRESSION &&
                else_term.type() == Term::Type::EXPRESSION) {
                const Expression& e1 = then_term.expression();
                const Expression& e2 = else_term.expression();
                $$ = if_then_else(cond, e1, e2);
            } else if (then_term.type() == Term::Type::FORMULA &&
                       else_term.type() == Term::Type::FORMULA) {
                //    if(cond) then f1 else f2
                // -> (cond => f1) ∧ (¬cond => f2)
                // -> (¬cond ∨ f1) ∧ (cond ∨ f2)
                const Formula& f1 = then_term.formula();
                const Formula& f2 = else_term.formula();
                $$ = (!cond || f1) && (cond || f2);
            } else {
                std::cerr << @1 << " : Type mismatch in `if (c) then t1 else t2`:" << std::endl
                          << "    t1 = " << then_term << std::endl
                          << "    t2 = " << else_term << std::endl;
                YYABORT;
            }
        }
        |       '(' TK_FORALL enter_scope '(' variable_sort_list ')' term exit_scope ')' {
	    const Variables& vars = $5.first;
            const Formula& domain = $5.second;
	    const Formula body = Smt2Driver::EliminateBooleanVariables(vars, $7.formula());
	    const Variables quantified_variables = intersect(vars, body.GetFreeVariables());
	    if (quantified_variables.empty()) {
	        $$ = body;
	    } else {
                $$ = forall(quantified_variables, imply(domain, body));
	    }
        }
        |       '(' TK_LET enter_scope let_binding_list term exit_scope ')' {
            $$ = $5;
        }
        |       DOUBLE {
            const Box::Interval i{StringToInterval($1)};
            const double parsed{std::stod($1)};
            if (i.diam() == 0) {
                // point => floating-point constant expression.
                $$ = i.mid();
            } else {
                // interval => real constant expression.
                $$ = real_constant(i.lb(), i.ub(), i.lb() == parsed);
            }
        }
        |       HEXFLOAT { $$ = $1; }
        |       INT { $$ = convert_int64_to_double($1); }
        |       SYMBOL {
            try {
                const Variable& var = driver.lookup_variable($1);
                if (var.get_type() == Variable::Type::BOOLEAN) {
                    $$ = Formula(var);
                } else {
                    $$ = Expression(var);
                }
            } catch (std::runtime_error& e) {
                std::cerr << @1 << " : " << e.what() << std::endl;
                YYABORT;
            }
        }
        |       '(' TK_PLUS term ')' {
            $$ = $3;
        }
        |       '(' TK_PLUS term term_list ')' {
            for (const Term& term : $4) {
                $3.mutable_expression() += term.expression();
            }
            $$ = $3;
        }
        |       '(' TK_MINUS term ')' {
            $$ = - $3.expression();
        }
        |       '(' TK_MINUS term term_list ')' {
            for (const Term& term : $4) {
                $3.mutable_expression() -= term.expression();
            }
            $$ = $3;
        }
        |       '(' TK_TIMES term term_list ')' {
            for (const Term& term : $4) {
                $3.mutable_expression() *= term.expression();
            }
            $$ = $3;
        }
        |       '(' TK_DIV term term_list ')' {
            for (const Term& term : $4) {
                $3.mutable_expression() /= term.expression();
            }
            $$ = $3;
        }
        |       '('TK_EXP term ')' {
            $$ = exp($3.expression());
        }
        |       '('TK_LOG term ')' {
            $$ = log($3.expression());
        }
        |       '('TK_ABS term ')' {
            $$ = abs($3.expression());
        }
        |       '('TK_SIN term ')' {
            $$ = sin($3.expression());
            }
        |       '('TK_COS term ')' {
            $$ = cos($3.expression());
            }
        |       '('TK_TAN term ')' {
            $$ = tan($3.expression());
            }
        |       '('TK_ASIN term ')' {
            $$ = asin($3.expression());
            }
        |       '('TK_ACOS term ')' {
            $$ = acos($3.expression());
            }
        |       '('TK_ATAN term ')' {
            $$ = atan($3.expression());
            }
        |       '('TK_ATAN2 term term ')' {
            $$ = atan2($3.expression(), $4.expression());
            }
        |       '('TK_SINH term ')' {
            $$ = sinh($3.expression());
            }
        |       '('TK_COSH term ')' {
            $$ = cosh($3.expression());
            }
        |       '('TK_TANH term ')' {
            $$ = tanh($3.expression());
            }
        |       '('TK_MIN term term ')' {
            $$ = min($3.expression(), $4.expression());
            }
        |       '('TK_MAX term term ')' {
            $$ = max($3.expression(), $4.expression());
            }
        |       '('TK_SQRT term ')' {
            $$ = sqrt($3.expression());
            }
        |       '('TK_POW term term ')' {
            $$ = pow($3.expression(), $4.expression());
            }
       |       '(' SYMBOL term_list ')' {
            $$ = driver.LookupFunction($2, $3);
            }
       ;

let_binding_list: '(' var_binding_list ')' {
            // Locals must be bound simultaneously.
            for (auto& binding : $2) {
                const std::string& name{ binding.first };
                const Term& term{ binding.second };
                const bool is_formula = term.type() == Term::Type::FORMULA;
                const Sort sort = is_formula ? Sort::Bool : Sort::Real;
                const Variable v{ driver.DeclareLocalVariable(name, sort) };
                if (is_formula) {
                    const Formula fv{v};
                    const Formula& ft{ term.formula() };
                    driver.mutable_context().Assert((fv && ft) || (!fv && !ft));
                } else {
                    driver.mutable_context().Assert(Expression{v} == term.expression());
                }
            }
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

name_sort: '(' SYMBOL sort ')' {
            $$ = Variable{driver.DeclareLocalVariable($2, $3)};
        }
        ;

name_sort_list: /* empty list */ { $$ = std::vector<Variable>{}; }
        |       name_sort_list name_sort {
            const Variable& v = $2;
	    $1.push_back(v);
	    $$ = $1;
        }
        ;


variable_sort_list: /* empty list */ { $$ = std::pair<Variables, Formula>(Variables{}, Formula::True()); }
        |       variable_sort variable_sort_list {
            const Variable& v = std::get<0>($1);
            const double lb = std::get<1>($1);
            const double ub = std::get<2>($1);
            $2.first.insert(v);
            if (std::isfinite(lb)) {
                $2.second = $2.second && (lb <= v);
            }
            if (std::isfinite(ub)) {
                $2.second = $2.second && (v <= ub);
            }
            $$ = $2;
        }
        ;

variable_sort: '(' SYMBOL sort ')' {
            const Variable v = driver.RegisterVariable($2, $3);
            const double inf = std::numeric_limits<double>::infinity();
            $$ = std::tuple<Variable, double, double>(v, -inf, inf);
        }
        |       '(' SYMBOL sort '[' term ',' term ']' ')' {
            const Variable v = driver.RegisterVariable($2, $3);
            const double lb = $5.expression().Evaluate();
            const double ub = $7.expression().Evaluate();
            $$ = std::tuple<Variable, double, double>(v, lb, ub);
        }
        ;

sort:           SYMBOL { $$ = ParseSort($1); }
                ;

var_binding_list: /* empty list */ {
            $$ = std::vector<std::pair<std::string, Term>>{};
        }
        | var_binding var_binding_list {
            $2.push_back($1);
            $$ = $2;
        }
        ;

var_binding: '(' SYMBOL term ')' {
            $$ = std::pair<std::string, Term>($2, $3);
        }
        ;


%% /*** Additional Code ***/
void dreal::Smt2Parser::error(const Smt2Parser::location_type& l,
                              const std::string& m) {
    driver.error(l, m);
}

#ifdef __clang__
#pragma clang diagnostic pop
#endif
#pragma GCC diagnostic pop
