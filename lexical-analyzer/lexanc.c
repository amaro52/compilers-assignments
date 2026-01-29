/* lex1.c         14 Feb 01; 31 May 12; 11 Jan 18; 20 Jan 24       */

/* This file contains code stubs for the lexical analyzer.
   Rename this file to be lexanc.c and fill in the stubs.    */

/* Copyright (c) 2024 Gordon S. Novak Jr. and
   The University of Texas at Austin. */

/*
    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
*/

#include <ctype.h>
#include <limits.h>
#include <math.h>
#include <stdio.h>
#include <string.h>

#include "lexan.h"
#include "token.h"

extern int CHARCLASS[];

/* Mapping reserved words to their reserved word numbers
   (including reserved words that are operators) */
typedef struct {
    char* word;
    int number;
} ReservedWord;

// OPERATOR RESERVED WORDS
static ReservedWord reserved_words_operators[] = {
    {"and", AND - OPERATOR_BIAS}, {"or", OR - OPERATOR_BIAS},   {"not", NOT - OPERATOR_BIAS},
    {"div", DIV - OPERATOR_BIAS}, {"mod", MOD - OPERATOR_BIAS}, {"in", IN - OPERATOR_BIAS},
};

// RESERVED WORDS
static ReservedWord reserved_words[] = {
    {"array", ARRAY - RESERVED_BIAS},
    {"begin", BEGINBEGIN - RESERVED_BIAS},
    {"case", CASE - RESERVED_BIAS},
    {"const", CONST - RESERVED_BIAS},
    {"do", DO - RESERVED_BIAS},
    {"downto", DOWNTO - RESERVED_BIAS},
    {"else", ELSE - RESERVED_BIAS},
    {"end", END - RESERVED_BIAS},
    {"file", FILEFILE - RESERVED_BIAS},
    {"for", FOR - RESERVED_BIAS},
    {"function", FUNCTION - RESERVED_BIAS},
    {"goto", GOTO - RESERVED_BIAS},
    {"if", IF - RESERVED_BIAS},
    {"label", LABEL - RESERVED_BIAS},
    {"nil", NIL - RESERVED_BIAS},
    {"of", OF - RESERVED_BIAS},
    {"packed", PACKED - RESERVED_BIAS},
    {"procedure", PROCEDURE - RESERVED_BIAS},
    {"program", PROGRAM - RESERVED_BIAS},
    {"record", RECORD - RESERVED_BIAS},
    {"repeat", REPEAT - RESERVED_BIAS},
    {"set", SET - RESERVED_BIAS},
    {"then", THEN - RESERVED_BIAS},
    {"to", TO - RESERVED_BIAS},
    {"type", TYPE - RESERVED_BIAS},
    {"while", WHILE - RESERVED_BIAS},
    {"var", VAR - RESERVED_BIAS},
    {"until", UNTIL - RESERVED_BIAS},
    {"with", WITH - RESERVED_BIAS},
    // ... add the rest from your token.h file
};

#define RESERVED_OPERATORS_LENGTH (sizeof(reserved_words_operators) / sizeof(ReservedWord))
#define RESERVED_WORDS_LENGTH (sizeof(reserved_words) / sizeof(ReservedWord))

/* Skip blanks and whitespace.  Expand this function to skip comments too. */
void skipblanks() {
    int c;
    int scanning = 1;  // flag to keep the loop going

    while (scanning) {
        c = peekchar();

        if (c == EOF) {
            scanning = 0;
        }

        // handle standard whitespace characters
        else if (c == ' ' || c == '\n' || c == '\t') {
            getchar();  // Consume the character
        }
        // handle curly brace comments { ... }
        else if (c == '{') {
            getchar();                                   // skip '{'
            while ((c = getchar()) != EOF && c != '}');  // skip characters until we hit '}' or EOF
        }

        // handle parentheses-star comments (* ... *)
        else if (c == '(' && peek2char() == '*') {
            getchar();  // skip '('
            getchar();  // skip '*'

            // loop until we find a '*' followed by a ')'
            while ((c = getchar()) != EOF) {
                if (c == '*' && peekchar() == ')') {
                    getchar();  // skip the closing ')'
                    break;
                }
            }
        } else {
            scanning = 0;  // not a whitespace or comment
        }
    }
}

/* Returns token with its assigned tokentype and whichval if token is an
   operator or a reserved word */
TOKEN get_reserved_word(TOKEN tok, int type, ReservedWord* table) {
    // assign table length based on type of reserved word
    int table_length;
    if (type == OPERATOR) {
        table_length = RESERVED_OPERATORS_LENGTH;
    } else if (type == RESERVED) {
        table_length = RESERVED_WORDS_LENGTH;
    }

    // search through the reserved word table
    for (int i = 0; i < table_length; i++) {
        if (strcmp(tok->stringval, table[i].word) == 0) {
            tok->tokentype = type;
            tok->whichval = table[i].number;

            return (tok);  // return tok if found
        }
    }

    return NULL;  // return NULL if not found (not a reserved word of given type)
}

/* Get identifiers and reserved words */
TOKEN identifier(TOKEN tok) {
    // save the first 15 characters of the identifier into tok->stringval
    int c, i;
    i = 0;
    while ((c = peekchar()) != EOF && (CHARCLASS[c] == ALPHA || CHARCLASS[c] == NUMERIC)) {
        c = getchar();

        if (i < (sizeof(tok->stringval) - 1)) {  // only the first 15 characteres are significant
            tok->stringval[i] = tolower(c);
            i = i + 1;
        }
    }
    tok->stringval[i] = '\0';  // end the string

    // check if tok is an operator or reserved word
    if (get_reserved_word(tok, OPERATOR, reserved_words_operators) ||
        get_reserved_word(tok, RESERVED, reserved_words)) {
        return tok;  // tok is either operator or reserved word
    } else {
        tok->tokentype = IDENTIFIERTOK;  // tok is neither operator nor reserved word
    }

    return (tok);
}

TOKEN getstring(TOKEN tok) {
    int c, i;
    i = 0;
    getchar();  // move cursor over opening quote
    while ((c = peekchar()) != EOF && i < 15) {
        c = getchar();

        if (c == '\'') {
            if (peekchar() == '\'') {  // handle doubled quotes
                c = getchar();         // get second quote
            } else {
                break;  // end of string
            }
        }

        if (i < 15) {
            tok->stringval[i] = c;
            i = i + 1;
        }
    }

    // move cursor to end of string if it was truncated
    while (c != EOF && c != '\'') {
        c = getchar();
    }

    tok->stringval[i] = '\0';
    tok->tokentype = STRINGTOK;

    return (tok);
}

/* Operators and Delimeters */
TOKEN special(TOKEN tok) {
    int c, c2;
    c = getchar();
    c2 = peekchar();

    switch (c) {
        case '+':
            tok->tokentype = OPERATOR;
            tok->whichval = PLUS - OPERATOR_BIAS;
            break;

        case '-':
            tok->tokentype = OPERATOR;
            tok->whichval = MINUS - OPERATOR_BIAS;
            break;

        case '*':
            tok->tokentype = OPERATOR;
            tok->whichval = TIMES - OPERATOR_BIAS;
            break;

        case '/':
            tok->tokentype = OPERATOR;
            tok->whichval = DIVIDE - OPERATOR_BIAS;
            break;

        case ':':
            if (c2 == '=') {
                getchar();
                tok->tokentype = OPERATOR;
                tok->whichval = ASSIGN - OPERATOR_BIAS;
            } else {
                tok->tokentype = DELIMITER;
                tok->whichval = COLON - DELIMITER_BIAS;
            }
            break;

        case '=':
            tok->tokentype = OPERATOR;
            tok->whichval = EQ - OPERATOR_BIAS;
            break;

        case '<':
            tok->tokentype = OPERATOR;
            if (c2 == '>') {
                getchar();
                tok->whichval = NE - OPERATOR_BIAS;
            } else if (c2 == '=') {
                getchar();
                tok->whichval = LE - OPERATOR_BIAS;
            } else {
                tok->whichval = LT - OPERATOR_BIAS;
            }
            break;

        case '>':
            tok->tokentype = OPERATOR;
            if (c2 == '=') {
                getchar();
                tok->whichval = GE - OPERATOR_BIAS;
            } else {
                tok->whichval = GT - OPERATOR_BIAS;
            }
            break;

        case '^':
            tok->tokentype = OPERATOR;
            tok->whichval = POINT - OPERATOR_BIAS;
            break;

        case '.':
            if (c2 == '.') {
                getchar();
                tok->tokentype = DELIMITER;
                tok->whichval = DOTDOT - DELIMITER_BIAS;
            } else {
                tok->tokentype = OPERATOR;
                tok->whichval = DOT - OPERATOR_BIAS;
            }
            break;

        case ',':
            tok->tokentype = DELIMITER;
            tok->whichval = COMMA - DELIMITER_BIAS;
            break;

        case ';':
            tok->tokentype = DELIMITER;
            tok->whichval = SEMICOLON - DELIMITER_BIAS;
            break;

        case '(':
            tok->tokentype = DELIMITER;
            tok->whichval = LPAREN - DELIMITER_BIAS;
            break;

        case ')':
            tok->tokentype = DELIMITER;
            tok->whichval = RPAREN - DELIMITER_BIAS;
            break;

        case '[':
            tok->tokentype = DELIMITER;
            tok->whichval = LBRACKET - DELIMITER_BIAS;
            break;

        case ']':
            tok->tokentype = DELIMITER;
            tok->whichval = RBRACKET - DELIMITER_BIAS;
            break;
    }

    return (tok);
}

/* Get and convert unsigned numbers of all types. */
TOKEN number(TOKEN tok) {
    double num = 0.0;
    int c, charval;
    int is_real = 0;

    while ((c = peekchar()) != EOF && CHARCLASS[c] == NUMERIC) {
        c = getchar();

        charval = (c - '0');
        num = num * 10.0 + charval;
    }

    // handle case for a decimal point (real number)
    // avoid cases like '..'
    if (peekchar() == '.' && CHARCLASS[peek2char()] == NUMERIC) {
        getchar();  // move over the '.'

        // process fractional part
        double divisor = 1.0;
        double fraction = 0.0;
        while ((c = peekchar()) != EOF && CHARCLASS[c] == NUMERIC) {
            c = getchar();

            charval = (c - '0');
            fraction = fraction * 10.0 + charval;
            divisor *= 10.0;
        }
        num = num + (fraction / divisor);  // one division to maintain precision

        is_real = 1;  // mark as real number
    }

    // handle scienfitic notation
    c = peekchar();  // consume 'e' or 'E'
    if (c == 'e' || c == 'E') {
        getchar();  // move over 'e' or 'E'
        is_real = 1;

        int sign = 1;
        int exponent = 0;

        // check for sign
        c = peekchar();
        if (c == '+' || c == '-') {
            getchar();  // move over sign
            if (c == '-') {
                sign = -1;
            }
        }

        // read exponent digits
        while ((c = peekchar()) != EOF && CHARCLASS[c] == NUMERIC) {
            c = getchar();

            charval = (c - '0');
            exponent = exponent * 10.0 + charval;
        }

        // apply exponent math
        double base = 10.0;
        num = num * pow(base, (double)(sign * exponent));
    }

    tok->tokentype = NUMBERTOK;

    // assign number type and value
    if (is_real) {
        tok->basicdt = REAL;

        // float overflow check
        if (is_real) {
            tok->basicdt = REAL;

            double float_limits[] = {1e38, 1e-38};

            if (num > float_limits[0] || (num > 0 && num < float_limits[1])) {
                printf("Floating number out of range\n");
                tok->realval = 0.0;
            } else {
                tok->realval = num;
            }
        } else {
            tok->realval = num;
        }
    } else {
        tok->basicdt = INTEGER;

        // integer overflow check
        if (num > 2147483647.0) {
            printf("Integer number out of range\n");
            tok->intval = (int)(long long)num;
        } else {
            tok->intval = (int)num;
        }
    }

    return (tok);
}
