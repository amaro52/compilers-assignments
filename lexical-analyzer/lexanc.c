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
    {"while", WHILE - RESERVED_BIAS},
    {"var", VAR - RESERVED_BIAS},
    {"until", UNTIL - RESERVED_BIAS},
    {"with", WITH - RESERVED_BIAS},
    // ... add the rest from your token.h file
};

/* Skip blanks and whitespace.  Expand this function to skip comments too. */
void skipblanks() {
    int c;
    while ((c = peekchar()) != EOF && (c == ' ' || c == '\n' || c == '\t')) getchar();
}

/* Returns token with its assigned tokentype and whichval if token is an
   operator or a reserved word */
TOKEN get_reserved_word(TOKEN tok, int type, ReservedWord* table) {
    int reserved_words_length = sizeof(*table) / sizeof(ReservedWord);
    for (int i = 0; i < reserved_words_length; i++) {
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
    tok->stringval[i] = '\0';

    // check if tok is an operator or reserved word
    if (get_reserved_word(tok, OPERATOR, reserved_words_operators) ||
        get_reserved_word(tok, RESERVED, reserved_words)) {
        return tok;  // tok is either operator or reserved word
    }

    tok->tokentype = IDENTIFIERTOK;  // tok is neither operator nor reserved word

    return (tok);
}

TOKEN getstring(TOKEN tok) {
    int c, i;
    i = 0;
    getchar();  // move cursor over opening quote
    while ((c = peekchar()) != EOF && c != '\'') {
        c = getchar();

        if (c == '\'' && peekchar() == '\'') {  // handle doubled quotes
            c = getchar();                      // get second quote
        }

        if (i < 15) {
            tok->stringval[i] = c;
            i = i + 1;
        }
    }
    getchar();  // move cursor over closing quote

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

        default:
            printf("Unrecognized special character: %c\n", c);
    }

    return (tok);
}

/* Get and convert unsigned numbers of all types. */
TOKEN number(TOKEN tok) {
    double num;
    int c, charval;
    num = 0;
    while ((c = peekchar()) != EOF && CHARCLASS[c] == NUMERIC) {
        c = getchar();

        charval = (c - '0');
        num = num * 10 + charval;
    }

    // check for a decimal point
    if (peekchar() == '.') {
        getchar();  // move over the '.'

        double weight = 0.1;

        // process fractional part
        while ((c = peekchar()) != EOF && CHARCLASS[c] == NUMERIC) {
            c = getchar();

            charval = (c - '0');
            num = num + charval * weight;
            weight /= 10.0;
        }

        tok->basicdt = REAL;
        tok->realval = num;
    } else {
        // standard integer
        tok->basicdt = INTEGER;
        tok->intval = (long)num;
    }
    tok->tokentype = NUMBERTOK;

    return (tok);
}
