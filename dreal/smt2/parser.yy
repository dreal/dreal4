%{

#include <string>

#include "dreal/smt2/command.h"
#include "dreal/smt2/logic.h"
#include "dreal/smt2/sort.h"
#include "dreal/util/symbolic.h"

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
%name-prefix="dreal"

/* set the parser's class identifier */
%define "parser_class_name" "Parser"

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
%parse-param { class Driver& driver }

/* verbose error messages */
%error-verbose


%union
{
    dreal::Sort               sortVal;
    int                       intVal;
    double                    doubleVal;
    std::string*              stringVal;
    Expression*               exprVal;
    Formula*                  formulaVal;
    std::vector<Formula>*     formulaListVal;
    std::vector<Expression>*  exprListVal;
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
%token TK_TRUE TK_FALSE TK_AND TK_OR TK_NOT

%token TK_MAXIMIZE TK_MINIMIZE

%token                 END          0        "end of file"
%token <doubleVal>     DOUBLE                "double"
%token <intVal>        INT                   "int"
%token <stringVal>     SYMBOL                "symbol"
%token <stringVal>     KEYWORD               "keyword"
%token <stringVal>     STRING                "string"

%type <sortVal>        sort
%type <exprVal>        expr
%type <exprListVal>    expr_list
%type <formulaVal>     formula
%type <formulaListVal> formula_list

%{

#include "dreal/smt2/driver.h"
#include "dreal/smt2/scanner.h"

/* this "connects" the bison parser in the driver to the flex scanner class
 * object. it defines the yylex() function call to pull the next token from the
 * current lexer object of the driver context. */
#undef yylex
#define yylex driver.lexer_->lex

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
        |       command_maximize
        |       command_minimize
        |       command_pop
        |       command_push
        |       command_set_info
        |       command_set_logic
        |       command_set_option
        ;

command_assert: '('TK_ASSERT formula ')' {
    driver
        .context_.Assert(*$3);
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
                    switch ($6) {
                      case Sort::Bool:
                        driver
                            .context_
                            .DeclareVariable(Variable{*$3, Variable::Type::BOOLEAN});
                        break;
                      case Sort::Int:
                        driver
                            .context_
                            .DeclareVariable(Variable{*$3, Variable::Type::INTEGER});
                        break;
                      case Sort::Real:
                        driver
                            .context_
                            .DeclareVariable(Variable{*$3, Variable::Type::CONTINUOUS});
                        break;
                    }
                    delete $3;
                }
        |
                '(' TK_DECLARE_FUN SYMBOL '(' ')' sort '[' expr ',' expr ']' ')' {
                    switch ($6) {
                      case Sort::Bool:
                        driver
                            .context_
                            .DeclareVariable(Variable{*$3, Variable::Type::BOOLEAN}, *$8, *$10);
                        break;
                      case Sort::Int:
                        driver
                            .context_
                            .DeclareVariable(Variable{*$3, Variable::Type::INTEGER}, *$8, *$10);
                        break;
                      case Sort::Real:
                        driver
                            .context_
                            .DeclareVariable(Variable{*$3, Variable::Type::CONTINUOUS}, *$8, *$10);
                        break;
                    }
                    delete $3;
                    delete $8;
                    delete $10;
                }
                ;

command_exit:   '('TK_EXIT ')' {
                    driver.context_.Exit();
                }
                ;

command_maximize: '(' TK_MAXIMIZE expr ')' {
                      driver.context_.Maximize(*$3);
                      delete $3;
                }
                ;

command_minimize: '(' TK_MINIMIZE expr ')' {
                      driver.context_.Minimize(*$3);
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
        |       '(' TK_SET_INFO KEYWORD DOUBLE ')' {
                    driver
                        .context_
                        .SetInfo(*$3, std::to_string($4));
                    delete $3;
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
                        .SetOption(*$3, std::to_string($4));
                    delete $3;
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
                    driver.context_.Push($3);
                    }
        ;

command_pop:   '(' TK_POP INT ')' {
                    driver.context_.Pop($3);
                    }
        ;

formula_list:   formula { $$ = new std::vector<Formula>(1, *$1); delete $1; }
        |       formula_list formula { $1->push_back(*$2); $$ = $1; delete $2; }
        ;

formula:
                /* SYMBOL { $$ = new Formula{driver.context_.lookup_variable(*$1)}; } */
                TK_TRUE { $$ = new Formula(Formula::True()); }
        |       TK_FALSE { $$ = new Formula(Formula::False()); }
        |       '('TK_EQ expr expr ')' { $$ = new Formula(*$3 == *$4); delete $3; delete $4; }
        |       '('TK_LT expr expr ')' { $$ = new Formula(*$3 < *$4); delete $3; delete $4; }
        |       '('TK_LTE expr expr ')' { $$ = new Formula(*$3 <= *$4); delete $3; delete $4; }
        |       '('TK_GT expr expr ')' { $$ = new Formula(*$3 > *$4); delete $3; delete $4; }
        |       '('TK_GTE expr expr ')' { $$ = new Formula(*$3 >= *$4); delete $3; delete $4; }
        |       '('TK_AND formula_list ')' {
            Formula* f = new Formula(Formula::True());
            for (const Formula& conjunct : *$3) {
                *f = *f && conjunct;
            }
            $$ = f;
            delete $3;
        }
        |       '('TK_OR formula_list ')' {
            Formula* f = new Formula(Formula::False());
            for (const Formula& conjunct : *$3) {
                *f = *f || conjunct;
            }
            $$ = f;
            delete $3;
        }
        |       '('TK_NOT formula ')' {
                    $$ = new Formula(!*$3);
                    delete $3;
        }
        ;

sort:           SYMBOL { $$ = ParseSort(*$1); delete $1; }
                ;

expr_list:      expr { $$ = new std::vector<Expression>(1, *$1); delete $1; }
        |       expr_list expr { $1->push_back(*$2); $$ = $1; delete $2; }

expr:           DOUBLE { $$ = new Expression{$1}; }
        |       INT { $$ = new Expression{static_cast<double>($1)}; }
        |       SYMBOL { $$ = new Expression{driver.context_.lookup_variable(*$1)}; delete $1; }
        |       '(' TK_PLUS expr expr_list ')' {
            for (const Expression& term : *$4) {
                *$3 += term;
            }
            $$ = $3;
            delete $4;
        }
        |       '(' TK_MINUS expr ')' {
            $$ = new Expression{-*$3};
            delete $3;
        }
        |       '(' TK_MINUS expr expr_list ')' {
            for (const Expression& term : *$4) {
                *$3 -= term;
            }
            $$ = $3;
            delete $4;
        }
        |       '(' TK_TIMES expr expr_list ')' {
            for (const Expression& term : *$4) {
                *$3 *= term;
            }
            $$ = $3;
            delete $4;
        }
        |       '(' TK_DIV expr expr_list ')' {
            for (const Expression& term : *$4) {
                *$3 /= term;
            }
            $$ = $3;
            delete $4;
        }
        |       '('TK_EXP expr ')' {
            $$ = new Expression{exp(*$3)};
            delete $3;
        }
        |       '('TK_LOG expr ')' {
            $$ = new Expression{log(*$3)};
            delete $3;
        }
        |       '('TK_ABS expr ')' {
            $$ = new Expression{abs(*$3)};
            delete $3;
        }
        |       '('TK_SIN expr ')' {
            $$ = new Expression{sin(*$3)};
            delete $3;
            }
        |       '('TK_COS expr ')' {
            $$ = new Expression{cos(*$3)};
            delete $3;
            }
        |       '('TK_TAN expr ')' {
            $$ = new Expression{tan(*$3)};
            delete $3;
            }
        |       '('TK_ASIN expr ')' {
            $$ = new Expression{asin(*$3)};
            delete $3;
            }
        |       '('TK_ACOS expr ')' {
            $$ = new Expression{acos(*$3)};
            delete $3;
            }
        |       '('TK_ATAN expr ')' {
            $$ = new Expression{atan(*$3)};
            delete $3;
            }
        |       '('TK_ATAN2 expr expr ')' {
            $$ = new Expression{atan2(*$3, *$4)};
            delete $3;
            delete $4;
            }
        |       '('TK_SINH expr ')' {
            $$ = new Expression{sinh(*$3)};
            delete $3;
            }
        |       '('TK_COSH expr ')' {
            $$ = new Expression{cosh(*$3)};
            delete $3;
            }
        |       '('TK_TANH expr ')' {
            $$ = new Expression{tanh(*$3)};
            delete $3;
            }
        |       '('TK_MIN expr expr ')' {
            $$ = new Expression{min(*$3, *$4)};
            delete $3;
            }
        |       '('TK_MAX expr expr ')' {
            $$ = new Expression{max(*$3, *$4)};
            delete $3;
            delete $4;
            }
        |       '('TK_SQRT expr ')' {
            $$ = new Expression{sqrt(*$3)};
            delete $3;
            }
        |       '('TK_POW expr expr ')' {
            $$ = new Expression{pow(*$3, *$4)};
            delete $3;
            delete $4;
            }
                ;

%% /*** Additional Code ***/
void dreal::Parser::error(const Parser::location_type& l,
                         const std::string& m)
{
    driver.error(l, m);
}
