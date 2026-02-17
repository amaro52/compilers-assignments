/* lexanc.c */

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

#include "token.h"
// token.h must be included before lexan.h because of the TOKEN type definition
#include "lexan.h"

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
#define UPPER_FLOAT_LIMIT 1e38
#define LOWER_FLOAT_LIMIT 1e-38

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

/* store first 15 characters of a string */
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
    double real_val = 0.0;
    long long int_val = 0;  // use long long to check for overflow
    int int_overflow = 0;   // flag to indicate if integer overflow occurred
    int c, charval;
    int is_real = 0;  // flag to indicate if number is real

    // process integer part
    while ((c = peekchar()) != EOF && CHARCLASS[c] == NUMERIC) {
        c = getchar();

        charval = (c - '0');
        real_val = real_val * 10.0 + charval;

        if (!int_overflow) {
            // check if adding this digit exceeds __INT_MAX__
            if (int_val > (__INT_MAX__ - charval) / 10) {
                int_overflow = 1;
            } else {
                int_val = int_val * 10 + charval;
            }
        }
    }

    // handle case for a decimal point (real number)
    // avoid cases like '..'
    c = peekchar();
    if (c == '.' && CHARCLASS[peek2char()] == NUMERIC) {
        getchar();    // move over the '.'
        is_real = 1;  // non-integer, so mark as real number

        double divisor = 1.0;
        double fraction = 0.0;
        while ((c = peekchar()) != EOF && CHARCLASS[c] == NUMERIC) {
            c = getchar();
            charval = (c - '0');

            fraction = fraction * 10.0 + charval;
            divisor *= 10.0;
        }
        real_val = real_val + (fraction / divisor);  // 1 division to maintain precision
    }

    // handle scienfitic notation
    c = peekchar();  // consume 'e' or 'E'
    if (c == 'e' || c == 'E') {
        getchar();  // move over 'e' or 'E'
        is_real = 1;

        int sign = 1;
        int exponent = 0;

        c = peekchar();  // check for sign
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
        real_val = real_val * pow(10.0, (double)(sign * exponent));  // apply exponent math
    }

    tok->tokentype = NUMBERTOK;

    // assign number type and value
    if (is_real) {
        tok->basicdt = REAL;

        if (real_val > UPPER_FLOAT_LIMIT || (real_val > 0 && real_val < LOWER_FLOAT_LIMIT)) {
            printf("Floating number out of range\n");
            tok->realval = 0.0;
        } else {
            tok->realval = real_val;
        }
    } else {
        tok->basicdt = INTEGER;
        if (int_overflow) {
            printf("Integer number out of range\n");
            tok->intval = (int)int_val;  // returns the frozen prefix
        } else {
            tok->intval = (int)int_val;
        }
    }

    return (tok);
}