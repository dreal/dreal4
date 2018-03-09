%{ /*** C/C++ Declarations ***/

#ifdef __clang__
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wdeprecated-register"
#pragma clang diagnostic ignored "-Wnull-conversion"
#pragma clang diagnostic ignored "-Wunneeded-internal-declaration"
#endif

/* ignore harmless bug in old versions of flex */
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wsign-compare"
#pragma GCC diagnostic ignored "-Wold-style-cast"

#include <string>

#include "dreal/dr/scanner.h"

/* import the parser's token type into a local typedef */
typedef dreal::DrParser::token token;
typedef dreal::DrParser::token_type token_type;

/* By default yylex returns int, we use token_type. Unfortunately yyterminate
 * by default returns 0, which is not of token_type. */
#define yyterminate() return token::END

/* This disables inclusion of unistd.h, which is not available under Visual C++
 * on Win32. The C++ scanner uses STL streams instead. */
#define YY_NO_UNISTD_H

%}

/*** Flex Declarations and Options ***/

/* enable c++ scanner class generation */
%option c++

/* change the name of the scanner class. results in "DrFlexLexer" */
%option prefix="Dr"

/* the manual says "somewhat more optimized" */
%option batch

/* enable scanner to generate debug output. disable this for release
 * versions. */
%option debug

/* no support for include files is planned */
%option yywrap nounput

/* enables the use of start condition stacks */
%option stack

%option yylineno
			
/* The following paragraph suffices to track locations accurately. Each time
 * yylex is invoked, the begin position is moved onto the end position. */
%{
/* handle locations */
int dr_yycolumn = 1;
    
#define YY_USER_ACTION yylloc->begin.line = yylloc->end.line = yylineno; \
yylloc->begin.column = dr_yycolumn; yylloc->end.column = dr_yycolumn+yyleng-1; \
dr_yycolumn += yyleng;
%}

%% /*** Regular Expressions Part ***/

%{
    // reset location
    yylloc->step();
%}

 /*** BEGIN - lexer rules ***/

"#".*[\n\r]+ {
    dr_yycolumn=1;
}

"var"                   { return DrParser::token::TK_VAR; }
"cost"                  { return DrParser::token::TK_COST; }
"prec"                  { return DrParser::token::TK_PREC; }
"ctr"                   { return DrParser::token::TK_CTR; }

"["                     { return DrParser::token::TK_LB; }
"]"                     { return DrParser::token::TK_RB; }
":"                     { return DrParser::token::TK_COLON; }
","                     { return DrParser::token::TK_COMMA; }
";"                     { return DrParser::token::TK_SEMICOLON; }

"+"                     { return DrParser::token::TK_PLUS; }
"-"                     { return DrParser::token::TK_MINUS; }
"*"                     { return DrParser::token::TK_TIMES; }
"/"                     { return DrParser::token::TK_DIV; }
"="                     { return DrParser::token::TK_EQ; }
"<="                    { return DrParser::token::TK_LTE; }
">="                    { return DrParser::token::TK_GTE; }
"<"                     { return DrParser::token::TK_LT; }
">"                     { return DrParser::token::TK_GT; }
"exp"                   { return DrParser::token::TK_EXP; }
"log"                   { return DrParser::token::TK_LOG; }
"abs"                   { return DrParser::token::TK_ABS; }
"sin"                   { return DrParser::token::TK_SIN; }
"cos"                   { return DrParser::token::TK_COS; }
"tan"                   { return DrParser::token::TK_TAN; }
"asin"|"arcsin"         { return DrParser::token::TK_ASIN; }
"acos"|"arccos"         { return DrParser::token::TK_ACOS; }
"atan"|"arctan"         { return DrParser::token::TK_ATAN; }
"atan2"|"arctan2"       { return DrParser::token::TK_ATAN2; }
"sinh"                  { return DrParser::token::TK_SINH; }
"cosh"                  { return DrParser::token::TK_COSH; }
"tanh"                  { return DrParser::token::TK_TANH; }
"min"                   { return DrParser::token::TK_MIN; }
"max"                   { return DrParser::token::TK_MAX; }
"sqrt"                  { return DrParser::token::TK_SQRT; }
"pow"                   { return DrParser::token::TK_POW; }
"^"                     { return DrParser::token::TK_CARET; }

"implies"               { return DrParser::token::TK_IMPLIES; }
"=>"                    { return DrParser::token::TK_IMPLIES; }
"and"                   { return DrParser::token::TK_AND; }
"or"                    { return DrParser::token::TK_OR; }
"not"                   { return DrParser::token::TK_NOT; }

 /* gobble up white-spaces */
[ \t\r]+ {
    yylloc->step();
}

 /* gobble up end-of-lines */
\n {
    dr_yycolumn=1;
}

(0|[1-9][0-9]*) {
    yylval->doubleVal = std::stod(yytext);
    return token::DOUBLE;
}

((([0-9]+)|([0-9]*\.?[0-9]+))([eE][-+]?[0-9]+)?)   {
    yylval->doubleVal = std::stod(yytext);
    return token::DOUBLE;
}

((([0-9]+)|([0-9]+\.)))                            {
    yylval->doubleVal = std::stod(yytext);
    return token::DOUBLE;
}

[a-zA-Z]([a-zA-Z0-9_\.])* {
    yylval->stringVal = new std::string(yytext, yyleng);
    return token::ID;
}

 /* pass all other characters up to bison */
. {
    return static_cast<token_type>(*yytext);
}
%% /*** Additional Code ***/

namespace dreal {

DrScanner::DrScanner(std::istream* in,
                     std::ostream* out)
    : DrFlexLexer(in, out) {}

DrScanner::~DrScanner() {}

void DrScanner::set_debug(const bool b) {
    yy_flex_debug = b;
}
}  // namespace dreal

/* This implementation of DrFlexLexer::yylex() is required to fill the
 * vtable of the class DrFlexLexer. We define the scanner's main yylex
 * function via YY_DECL to reside in the DrScanner class instead. */

#ifdef yylex
#undef yylex
#endif

int DrFlexLexer::yylex()
{
    std::cerr << "in DrlexLexer::yylex() !" << std::endl;
    return 0;
}

/* When the scanner receives an end-of-file indication from YY_INPUT, it then
 * checks the yywrap() function. If yywrap() returns false (zero), then it is
 * assumed that the function has gone ahead and set up `yyin' to point to
 * another input file, and scanning continues. If it returns true (non-zero),
 * then the scanner terminates, returning 0 to its caller. */

int DrFlexLexer::yywrap()
{
    return 1;
}

#pragma GCC diagnostic pop
#ifdef __clang__
#pragma clang diagnostic pop
#endif
