%{ /*** C/C++ Declarations ***/

#ifdef __clang__
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wdeprecated-register"
#pragma clang diagnostic ignored "-Wnull-conversion"
#pragma clang diagnostic ignored "-Wunneeded-internal-declaration"
#endif

/* ignore harmless bug in old versions of flex */
#pragma GCC diagnostic ignored "-Wsign-compare"

#include <string>

#include "dreal/smt2/scanner.h"

/* import the parser's token type into a local typedef */
typedef dreal::Parser::token token;
typedef dreal::Parser::token_type token_type;

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

/* change the name of the scanner class. results in "Smt2FlexLexer" */
%option prefix="Smt2"

/* the manual says "somewhat more optimized" */
%option batch

/* enable scanner to generate debug output. disable this for release
 * versions. */
%option debug

/* no support for include files is planned */
%option yywrap nounput

/* enables the use of start condition stacks */
%option stack

/* The following paragraph suffices to track locations accurately. Each time
 * yylex is invoked, the begin position is moved onto the end position. */
%{
#define YY_USER_ACTION  yylloc->columns(yyleng);
%}

whitespace      [\x09 \xA0]
printable_char  [\x20-\x7E\xA0-xFF]
digit           [0-9]
letter          [a-zA-Z]
numeral         0|[1-9][0-9]*
decimal         {numeral}\.0*{numeral}
hexadecimal     "#x"[0-9A-Fa-f]+
binary          "#b"[01]+
special_char    [+\-/*=%?!.$_~&^<>@]
sym_begin       {letter}|{special_char}
sym_continue    {sym_begin}|{digit}
simple_symbol   {sym_begin}{sym_continue}*

%x str
%x quoted

%% /*** Regular Expressions Part ***/

%{
    // reset location
    yylloc->step();
%}

 /*** BEGIN - lexer rules ***/

";".*[\n\r]+ {
    yylloc->lines(yyleng); yylloc->step();
}

"!"                     { return Parser::token::TK_EXCLAMATION; }
"BINARY"                { return Parser::token::TK_BINARY; }
"DECIMAL"               { return Parser::token::TK_DECIMAL; }
"HEXADECIMAL"           { return Parser::token::TK_HEXADECIMAL; }
"NUMERAL"               { return Parser::token::TK_NUMERAL; }
"STRING"                { return Parser::token::TK_STRING; }
"_"                     { return Parser::token::TK_UNDERSCORE; }
"as"                    { return Parser::token::TK_AS; }
"exists"                { return Parser::token::TK_EXISTS; }
"forall"                { return Parser::token::TK_FORALL; }
"let"                   { return Parser::token::TK_LET; }
"par"                   { return Parser::token::TK_PAR; }

"assert"                { return Parser::token::TK_ASSERT; }
"check-sat"             { return Parser::token::TK_CHECK_SAT; }
"check-sat-assuming"    { return Parser::token::TK_CHECK_SAT_ASSUMING; }
"declare-const"         { return Parser::token::TK_DECLARE_CONST; }
"declare-fun"           { return Parser::token::TK_DECLARE_FUN; }
"declare-sort"          { return Parser::token::TK_DECLARE_SORT; }
"define-fun"            { return Parser::token::TK_DEFINE_FUN; }
"define-fun-rec"        { return Parser::token::TK_DEFINE_FUN_REC; }
"define-sort"           { return Parser::token::TK_DEFINE_SORT; }
"echo"                  { return Parser::token::TK_ECHO; }
"exit"                  { return Parser::token::TK_EXIT; }
"get-assertions"        { return Parser::token::TK_GET_ASSERTIONS; }
"get-assignment"        { return Parser::token::TK_GET_ASSIGNMENT; }
"get-info"              { return Parser::token::TK_GET_INFO; }
"get-model"             { return Parser::token::TK_GET_MODEL; }
"get-option"            { return Parser::token::TK_GET_OPTION; }
"get-proof"             { return Parser::token::TK_GET_PROOF; }
"get-unsat-assumptions" { return Parser::token::TK_GET_UNSAT_ASSUMPTIONS; }
"get-unsat-core"        { return Parser::token::TK_GET_UNSAT_CORE; }
"get-value"             { return Parser::token::TK_GET_VALUE; }
"pop"                   { return Parser::token::TK_POP; }
"push"                  { return Parser::token::TK_PUSH; }
"reset"                 { return Parser::token::TK_RESET; }
"reset-assertions"      { return Parser::token::TK_RESET_ASSERTIONS; }
"set-info"              { return Parser::token::TK_SET_INFO; }
"set-logic"             { return Parser::token::TK_SET_LOGIC; }
"set-option"            { return Parser::token::TK_SET_OPTION; }

"+"                     { return Parser::token::TK_PLUS; }
"-"                     { return Parser::token::TK_MINUS; }
"*"                     { return Parser::token::TK_TIMES; }
"/"                     { return Parser::token::TK_DIV; }
"="                     { return Parser::token::TK_EQ; }
"<="                    { return Parser::token::TK_LTE; }
">="                    { return Parser::token::TK_GTE; }
"<"                     { return Parser::token::TK_LT; }
">"                     { return Parser::token::TK_GT; }
"exp"                   { return Parser::token::TK_EXP; }
"log"                   { return Parser::token::TK_LOG; }
"abs"                   { return Parser::token::TK_ABS; }
"sin"                   { return Parser::token::TK_SIN; }
"cos"                   { return Parser::token::TK_COS; }
"tan"                   { return Parser::token::TK_TAN; }
"asin"|"arcsin"         { return Parser::token::TK_ASIN; }
"acos"|"arccos"         { return Parser::token::TK_ACOS; }
"atan"|"arctan"         { return Parser::token::TK_ATAN; }
"atan2"|"arctan2"       { return Parser::token::TK_ATAN2; }
"sinh"                  { return Parser::token::TK_SINH; }
"cosh"                  { return Parser::token::TK_COSH; }
"tanh"                  { return Parser::token::TK_TANH; }
"min"                   { return Parser::token::TK_MIN; }
"max"                   { return Parser::token::TK_MAX; }
"maximize"              { return Parser::token::TK_MAXIMIZE; }
"minimize"              { return Parser::token::TK_MINIMIZE; }
"sqrt"                  { return Parser::token::TK_SQRT; }
"^"|"pow"               { return Parser::token::TK_POW; }

"true"                  { return Parser::token::TK_TRUE; }
"false"                 { return Parser::token::TK_FALSE; }
"and"                   { return Parser::token::TK_AND; }
"or"                    { return Parser::token::TK_OR; }
"not"                   { return Parser::token::TK_NOT; }
"ite"                   { return Parser::token::TK_ITE; }

 /* gobble up white-spaces */
[ \t\r]+ {
    yylloc->step();
}

 /* gobble up end-of-lines */
\n {
    yylloc->lines(yyleng); yylloc->step();
}

[-+]?(0|[1-9][0-9]*) {
    yylval->intVal = atoi(yytext);
    return token::INT;
}

[-+]?((([0-9]+)|([0-9]*\.?[0-9]+))([eE][-+]?[0-9]+)?)   {
    yylval->doubleVal = atof(yytext);
    return token::DOUBLE;
}

[-+]?((([0-9]+)|([0-9]+\.)))                            {
    yylval->doubleVal = atof(yytext);
    return token::DOUBLE;
}

"-"?"0"("x"|"X")[0-9]\.[0-9a-fA-F]+"p"("+"|"-")?[0-9]+  {
    yylval->doubleVal = atof(yytext);
    return token::DOUBLE;
}

{simple_symbol} {
    yylval->stringVal = new std::string(yytext, yyleng);
    return token::SYMBOL;
}

":"{simple_symbol} {
    yylval->stringVal = new std::string(yytext, yyleng);;
    return token::KEYWORD;
}

\"                      { BEGIN str; yymore(); }
<str>\"\"               { yymore(); }
<str>[\n\r]+            { yymore(); }
<str>\"                 {
    BEGIN 0;
    yylval->stringVal = new std::string(yytext, yyleng);;
    return token::STRING;
}
<str>.                  { yymore(); }

\|                      { BEGIN quoted; yymore(); }
<quoted>[\n\r]+         { yymore(); }
<quoted>\|              {
    BEGIN 0;
    yylval->stringVal = new std::string(yytext, yyleng);;
    return token::SYMBOL;
}
<quoted>\\              { }
<quoted>.               { yymore(); }

 /* pass all other characters up to bison */
. {
    return static_cast<token_type>(*yytext);
}
%% /*** Additional Code ***/

namespace dreal {

Scanner::Scanner(std::istream* in,
                 std::ostream* out)
    : Smt2FlexLexer(in, out) {}

Scanner::~Scanner() {}

void Scanner::set_debug(const bool b) {
    yy_flex_debug = b;
}
}  // namespace dreal

/* This implementation of Smt2FlexLexer::yylex() is required to fill the
 * vtable of the class Smt2FlexLexer. We define the scanner's main yylex
 * function via YY_DECL to reside in the Scanner class instead. */

#ifdef yylex
#undef yylex
#endif

int Smt2FlexLexer::yylex()
{
    std::cerr << "in Smt2lexLexer::yylex() !" << std::endl;
    return 0;
}

/* When the scanner receives an end-of-file indication from YY_INPUT, it then
 * checks the yywrap() function. If yywrap() returns false (zero), then it is
 * assumed that the function has gone ahead and set up `yyin' to point to
 * another input file, and scanning continues. If it returns true (non-zero),
 * then the scanner terminates, returning 0 to its caller. */

int Smt2FlexLexer::yywrap()
{
    return 1;
}

#ifdef __clang__
#pragma clang diagnostic pop
#endif
