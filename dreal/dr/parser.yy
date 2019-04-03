%{

#include <iostream>
#include <string>

#include "dreal/symbolic/symbolic.h"

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
%define parser_class_name {DrParser}

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
%parse-param { class DrDriver& driver }

/* verbose error messages */
%define parse.error verbose


%union
{
    double                    doubleVal;
    std::string*              stringVal;
    Expression*               exprVal;
    Formula*                  formulaVal;
}

%token TK_VAR TK_COST TK_PREC TK_CTR

%token TK_PLUS TK_MINUS TK_TIMES TK_DIV
%token TK_EQ TK_LTE TK_GTE TK_LT TK_GT
%token TK_EXP TK_LOG TK_ABS TK_SIN TK_COS TK_TAN TK_ASIN TK_ACOS TK_ATAN TK_ATAN2
%token TK_SINH TK_COSH TK_TANH TK_MIN TK_MAX TK_SQRT TK_POW TK_CARET
%token TK_AND TK_OR TK_NOT TK_IMPLIES

%token TK_LB TK_RB TK_COLON TK_COMMA TK_SEMICOLON

%token                 END          0        "end of file"
%token <doubleVal>     DOUBLE                "double"
%token <stringVal>     ID                    "identifier"

%type <exprVal>        expr
%type <formulaVal>     formula

%nonassoc TK_EQ TK_NEQ TK_LT TK_LEQ TK_GT TK_GEQ
%left TK_PLUS TK_MINUS
%left TK_TIMES TK_DIV
%left UMINUS
%right TK_CARET

%right TK_IMPLIES
%left TK_OR
%left TK_AND
%left TK_NOT

%{

#include "dreal/dr/driver.h"
#include "dreal/dr/scanner.h"

/* this "connects" the bison parser in the driver to the flex scanner class
 * object. it defines the yylex() function call to pull the next token from the
 * current lexer object of the driver context. */
#undef yylex
#define yylex driver.scanner_->lex

%}

%% /*** Grammar Rules ***/

script:         var_decl_sec
                opt_ctr_decl_sec
		opt_cost_decl_sec
		{
                    driver.Solve();
		}
		;

// =============================
// Variable Declaration Section
// =============================
var_decl_sec:   TK_VAR TK_COLON var_decl_list
        ;

var_decl_list:  var_decl
        |       var_decl var_decl_list
        ;

var_decl:       TK_LB expr TK_COMMA expr TK_RB ID TK_SEMICOLON {
                    driver.DeclareVariable(Variable{*$6, Variable::Type::CONTINUOUS}, $2->Evaluate(), $4->Evaluate());
                    delete $2;
                    delete $4;
                    delete $6;
                }
        |       expr ID TK_SEMICOLON {
                    driver.DeclareVariable(Variable{*$2, Variable::Type::CONTINUOUS}, $1->Evaluate(), $1->Evaluate());
                    delete $1;
                    delete $2;
        }
        ;

// =============================
// Constraints
// =============================
opt_ctr_decl_sec:   /* nothing */
	|	ctr_decl_sec
	;

ctr_decl_sec:   TK_CTR TK_COLON ctr_decl_list
        ;

ctr_decl_list:  ctr_decl
        |       ctr_decl ctr_decl_list
        ;

ctr_decl:        formula TK_SEMICOLON {
                     driver.Assert(*$1);
                     delete $1;
        }
        ;

// ====
// Cost
// ====
opt_cost_decl_sec: /* nothing */
	|	 TK_COST TK_COLON cost_decl_list
	;

cost_decl_list:  cost_decl
	| 	cost_decl cost_decl_list
	;

cost_decl:     expr TK_SEMICOLON {
                     driver.Minimize(*$1);
                     delete $1;
        }
        ;

// =======
// Formula
// =======
formula:
                expr TK_EQ expr { $$ = new Formula(*$1 == *$3); delete $1; delete $3; }
        |       expr TK_LT expr { $$ = new Formula(*$1 < *$3); delete $1; delete $3; }
        |       expr TK_LTE expr { $$ = new Formula(*$1 <= *$3); delete $1; delete $3; }
        |       expr TK_GT expr { $$ = new Formula(*$1 > *$3); delete $1; delete $3; }
        |       expr TK_GTE expr { $$ = new Formula(*$1 >= *$3); delete $1; delete $3; }
        |       formula TK_AND formula {
            $$ = new Formula(*$1 && *$3);
            delete $1;
            delete $3;
        }
        |       formula TK_OR formula {
            $$ = new Formula(*$1 || *$3);
            delete $1;
            delete $3;
        }
        |       formula TK_IMPLIES formula {
            $$ = new Formula(!*$1 || *$3);
            delete $1;
            delete $3;
        }
        |       TK_NOT formula {
            $$ = new Formula(!*$2);
            delete $2;
        }
        |       '(' formula ')' {
            $$ = $2;
        }
        ;

// ==========
// Expression
// ==========
expr:           DOUBLE { $$ = new Expression{$1}; }
        |       ID {
	    try {
		const Variable& var = driver.lookup_variable(*$1);
	        $$ = new Expression{var};
            } catch (std::runtime_error& e) {
		std::cerr << @1 << " : " << e.what() << std::endl;
		delete $1;		
		YYABORT;
	    }
	    delete $1;		
	}
        |       expr TK_PLUS expr {
            $$ = new Expression(*$1 + *$3);
            delete $1;
            delete $3;
        }
        |       TK_MINUS expr %prec UMINUS {
            $$ = new Expression{-*$2};
            delete $2;
        }
        |       expr TK_MINUS expr {
            $$ = new Expression(*$1 - *$3);
            delete $1;
            delete $3;
        }
        |       expr TK_TIMES expr {
            $$ = new Expression(*$1 * *$3);
            delete $1;
            delete $3;
        }
        |       expr TK_DIV expr {
            $$ = new Expression(*$1 / *$3);
            delete $1;
            delete $3;
        }
        |       TK_EXP '(' expr ')' {
            $$ = new Expression{exp(*$3)};
            delete $3;
        }
        |       TK_LOG '(' expr ')' {
            $$ = new Expression{log(*$3)};
            delete $3;
        }
        |       TK_ABS '(' expr ')' {
            $$ = new Expression{abs(*$3)};
            delete $3;
        }
        |       TK_SIN '(' expr ')' {
            $$ = new Expression{sin(*$3)};
            delete $3;
            }
        |       TK_COS '(' expr ')' {
            $$ = new Expression{cos(*$3)};
            delete $3;
            }
        |       TK_TAN '(' expr ')' {
            $$ = new Expression{tan(*$3)};
            delete $3;
            }
        |       TK_ASIN '(' expr ')' {
            $$ = new Expression{asin(*$3)};
            delete $3;
            }
        |       TK_ACOS '(' expr ')' {
            $$ = new Expression{acos(*$3)};
            delete $3;
            }
        |       TK_ATAN '(' expr ')' {
            $$ = new Expression{atan(*$3)};
            delete $3;
            }
        |       TK_ATAN2 '(' expr TK_COMMA expr ')' {
            $$ = new Expression{atan2(*$3, *$5)};
            delete $3;
            delete $5;
            }
        |       TK_SINH '(' expr ')' {
            $$ = new Expression{sinh(*$3)};
            delete $3;
            }
        |       TK_COSH '(' expr ')' {
            $$ = new Expression{cosh(*$3)};
            delete $3;
            }
        |       TK_TANH '(' expr ')' {
            $$ = new Expression{tanh(*$3)};
            delete $3;
            }
        |       TK_MIN '(' expr TK_COMMA expr ')' {
            $$ = new Expression{min(*$3, *$5)};
            delete $3;
            delete $5;
            }
        |       TK_MAX '(' expr TK_COMMA expr ')' {
            $$ = new Expression{max(*$3, *$5)};
            delete $3;
            delete $5;
            }
        |       TK_SQRT '(' expr ')' {
            $$ = new Expression{sqrt(*$3)};
            delete $3;
            }
        |       TK_POW '(' expr TK_COMMA expr ')' {
            $$ = new Expression{pow(*$3, *$5)};
            delete $3;
            delete $5;
            }
        |       expr TK_CARET expr {
            $$ = new Expression{pow(*$1, *$3)};
            delete $1;
            delete $3;
            }
        |       '(' expr ')' {
            $$ = $2;
        }
        ;

%% /*** Additional Code ***/
void dreal::DrParser::error(const DrParser::location_type& l,
                            const std::string& m) {
    driver.error(l, m);
}

#pragma GCC diagnostic pop
