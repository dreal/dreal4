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

#include "dreal/smt2/scanner.h"

/* import the parser's token type into a local typedef */
typedef dreal::Smt2Parser::token token;
typedef dreal::Smt2Parser::token_type token_type;

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

%option yylineno
                        
/* The following paragraph suffices to track locations accurately. Each time
 * yylex is invoked, the begin position is moved onto the end position. */
%{
/* handle locations */
int smt2_yycolumn = 1;
    
#define YY_USER_ACTION yylloc->begin.line = yylloc->end.line = yylineno; \
yylloc->begin.column = smt2_yycolumn; yylloc->end.column = smt2_yycolumn+yyleng-1; \
smt2_yycolumn += yyleng;
%}

whitespace      [\x09 \xA0]
printable_char  [\x20-\x7E\xA0-xFF]
digit           [0-9]
hex             [0-9a-fA-F]
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
    smt2_yycolumn=1;
}

"!"                     { return Smt2Parser::token::TK_EXCLAMATION; }
"BINARY"                { return Smt2Parser::token::TK_BINARY; }
"DECIMAL"               { return Smt2Parser::token::TK_DECIMAL; }
"HEXADECIMAL"           { return Smt2Parser::token::TK_HEXADECIMAL; }
"NUMERAL"               { return Smt2Parser::token::TK_NUMERAL; }
"STRING"                { return Smt2Parser::token::TK_STRING; }
"_"                     { return Smt2Parser::token::TK_UNDERSCORE; }
"as"                    { return Smt2Parser::token::TK_AS; }
"exists"                { return Smt2Parser::token::TK_EXISTS; }
"forall"                { return Smt2Parser::token::TK_FORALL; }
"let"                   { return Smt2Parser::token::TK_LET; }
"par"                   { return Smt2Parser::token::TK_PAR; }

"assert"                { return Smt2Parser::token::TK_ASSERT; }
"check-sat"             { return Smt2Parser::token::TK_CHECK_SAT; }
"check-sat-assuming"    { return Smt2Parser::token::TK_CHECK_SAT_ASSUMING; }
"declare-const"         { return Smt2Parser::token::TK_DECLARE_CONST; }
"declare-fun"           { return Smt2Parser::token::TK_DECLARE_FUN; }
"declare-sort"          { return Smt2Parser::token::TK_DECLARE_SORT; }
"define-fun"            { return Smt2Parser::token::TK_DEFINE_FUN; }
"define-fun-rec"        { return Smt2Parser::token::TK_DEFINE_FUN_REC; }
"define-sort"           { return Smt2Parser::token::TK_DEFINE_SORT; }
"echo"                  { return Smt2Parser::token::TK_ECHO; }
"exit"                  { return Smt2Parser::token::TK_EXIT; }
"get-assertions"        { return Smt2Parser::token::TK_GET_ASSERTIONS; }
"get-assignment"        { return Smt2Parser::token::TK_GET_ASSIGNMENT; }
"get-info"              { return Smt2Parser::token::TK_GET_INFO; }
"get-model"             { return Smt2Parser::token::TK_GET_MODEL; }
"get-option"            { return Smt2Parser::token::TK_GET_OPTION; }
"get-proof"             { return Smt2Parser::token::TK_GET_PROOF; }
"get-unsat-assumptions" { return Smt2Parser::token::TK_GET_UNSAT_ASSUMPTIONS; }
"get-unsat-core"        { return Smt2Parser::token::TK_GET_UNSAT_CORE; }
"get-value"             { return Smt2Parser::token::TK_GET_VALUE; }
"pop"                   { return Smt2Parser::token::TK_POP; }
"push"                  { return Smt2Parser::token::TK_PUSH; }
"reset"                 { return Smt2Parser::token::TK_RESET; }
"reset-assertions"      { return Smt2Parser::token::TK_RESET_ASSERTIONS; }
"set-info"              { return Smt2Parser::token::TK_SET_INFO; }
"set-logic"             { return Smt2Parser::token::TK_SET_LOGIC; }
"set-option"            { return Smt2Parser::token::TK_SET_OPTION; }

"+"                     { return Smt2Parser::token::TK_PLUS; }
"-"                     { return Smt2Parser::token::TK_MINUS; }
"*"                     { return Smt2Parser::token::TK_TIMES; }
"/"                     { return Smt2Parser::token::TK_DIV; }
"="                     { return Smt2Parser::token::TK_EQ; }
"<="                    { return Smt2Parser::token::TK_LTE; }
">="                    { return Smt2Parser::token::TK_GTE; }
"<"                     { return Smt2Parser::token::TK_LT; }
">"                     { return Smt2Parser::token::TK_GT; }
"exp"                   { return Smt2Parser::token::TK_EXP; }
"log"                   { return Smt2Parser::token::TK_LOG; }
"abs"                   { return Smt2Parser::token::TK_ABS; }
"sin"                   { return Smt2Parser::token::TK_SIN; }
"cos"                   { return Smt2Parser::token::TK_COS; }
"tan"                   { return Smt2Parser::token::TK_TAN; }
"asin"|"arcsin"         { return Smt2Parser::token::TK_ASIN; }
"acos"|"arccos"         { return Smt2Parser::token::TK_ACOS; }
"atan"|"arctan"         { return Smt2Parser::token::TK_ATAN; }
"atan2"|"arctan2"       { return Smt2Parser::token::TK_ATAN2; }
"sinh"                  { return Smt2Parser::token::TK_SINH; }
"cosh"                  { return Smt2Parser::token::TK_COSH; }
"tanh"                  { return Smt2Parser::token::TK_TANH; }
"min"                   { return Smt2Parser::token::TK_MIN; }
"max"                   { return Smt2Parser::token::TK_MAX; }
"maximize"              { return Smt2Parser::token::TK_MAXIMIZE; }
"minimize"              { return Smt2Parser::token::TK_MINIMIZE; }
"sqrt"                  { return Smt2Parser::token::TK_SQRT; }
"^"|"pow"               { return Smt2Parser::token::TK_POW; }

"true"                  { return Smt2Parser::token::TK_TRUE; }
"false"                 { return Smt2Parser::token::TK_FALSE; }
"and"                   { return Smt2Parser::token::TK_AND; }
"or"                    { return Smt2Parser::token::TK_OR; }
"not"                   { return Smt2Parser::token::TK_NOT; }
"ite"                   { return Smt2Parser::token::TK_ITE; }
"=>"                    { return Smt2Parser::token::TK_IMPLIES; }

 /* gobble up white-spaces */
[ \t\r]+ {
    yylloc->step();
}

 /* gobble up end-of-lines */
\n {
    smt2_yycolumn=1;
}

[-+]?(0|[1-9][0-9]*) {
    try {
        static_assert(sizeof(std::int64_t) == sizeof(long),
	              "sizeof(std::int64_t) != sizeof(long).");
        yylval->int64Val = std::stol(yytext);
        return token::INT;
    } catch(std::out_of_range& e) {
        std::cerr << "At line " << yylloc->begin.line
                  << " the following value would fall out of the range of the result type (long):\n"
                  << yytext << "\n";
        throw e;
    }
}

[-+]?((([0-9]+)|([0-9]*\.?[0-9]+))([eE][-+]?[0-9]+)?)   {
    yylval->doubleVal = new std::string(yytext, yyleng);
    return token::DOUBLE;
}

[-+]?((([0-9]+)|([0-9]+\.)))                            {
    yylval->doubleVal = new std::string(yytext, yyleng);
    return token::DOUBLE;
}

[-+]?0[xX]({hex}+\.?|{hex}*\.{hex}+)([pP][-+]?[0-9]+)? {
    yylval->hexfloatVal = std::stod(yytext);
    return token::HEXFLOAT;
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

Smt2Scanner::Smt2Scanner(std::istream* in,
                         std::ostream* out)
    : Smt2FlexLexer(in, out) {}

Smt2Scanner::~Smt2Scanner() {}

void Smt2Scanner::set_debug(const bool b) {
    yy_flex_debug = b;
}
}  // namespace dreal

/* This implementation of Smt2FlexLexer::yylex() is required to fill the
 * vtable of the class Smt2FlexLexer. We define the scanner's main yylex
 * function via YY_DECL to reside in the Smt2Scanner class instead. */

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

#pragma GCC diagnostic pop

#ifdef __clang__
#pragma clang diagnostic pop
#endif
