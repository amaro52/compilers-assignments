/* pars1c.c    Pascal Parser      Gordon S. Novak Jr.    19 Jul 22    */

/* This file contains a parser for a Pascal subset using the techniques of
   recursive descent and operator precedence.  The Pascal subset is equivalent
   to the one handled by the Yacc version pars1.y .  */

/* Copyright (c) 2022 Gordon S. Novak Jr. and
   The University of Texas at Austin. */

/* This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 2 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License (file gpl.text) for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA. */

/* To use:
                     make pars1c
                     pars1c
                     i:=j .

                     pars1c
                     begin i:=j; if i+j then x:=a+b*c else x:=a*b+c; k:=i end.

                     pars1c
                     if x+y then if y+z then i:=j else k:=2.
*/

/* You may copy this file to be parsc.c, expand it for your assignment,
   then use    make parsec    as above.  */

#include <ctype.h>
#include <stdio.h>

#include "codegen.h"
#include "lexan.h"
#include "parse.h"
#include "pprint.h"
#include "symtab.h"
#include "token.h"

TOKEN parseresult;
TOKEN savedtoken;

#define DEBUG 127      /* set bits here for debugging, 0 = off  */
#define DB_CONS 1      /* bit to trace cons */
#define DB_BINOP 2     /* bit to trace binop */
#define DB_MAKEIF 4    /* bit to trace makeif */
#define DB_MAKEPROGN 8 /* bit to trace makeprogn */
#define DB_PARSERES 16 /* bit to trace parseresult */
#define DB_GETTOK 32   /* bit to trace gettok */
#define DB_EXPR 64     /* bit to trace expr */

/* add item to front of list */
TOKEN cons(TOKEN item, TOKEN list) {
    item->link = list;
    if (DEBUG & DB_CONS) {
        printf("cons\n");
        dbugprinttok(item);
        dbugprinttok(list);
    };
    return item;
}

/* reduce binary operator */
/* operator, left-hand side, right-hand side */
TOKEN binop(TOKEN op, TOKEN lhs, TOKEN rhs) {
    op->operands = lhs; /* link operands to operator       */
    lhs->link = rhs;    /* link second operand to first    */
    rhs->link = NULL;   /* terminate operand list          */
    if (DEBUG & DB_BINOP) {
        printf("binop\n");
        dbugprinttok(op);  /*       op         =  (op lhs rhs)      */
        dbugprinttok(lhs); /*      /                                */
        dbugprinttok(rhs); /*    lhs --- rhs                        */
    };
    return op;
}

TOKEN makeif(TOKEN tok, TOKEN exp, TOKEN thenpart, TOKEN elsepart) {
    tok->tokentype = OPERATOR; /* Make it look like an operator   */
    tok->whichval = IFOP;
    if (elsepart != NULL) elsepart->link = NULL;
    thenpart->link = elsepart;
    exp->link = thenpart;
    tok->operands = exp;
    if (DEBUG & DB_MAKEIF) {
        printf("makeif\n");
        dbugprinttok(tok);
        dbugprinttok(exp);
        dbugprinttok(thenpart);
        dbugprinttok(elsepart);
    };
    return tok;
}

TOKEN makeprogn(TOKEN tok, TOKEN statements) {
    tok->tokentype = OPERATOR;
    tok->whichval = PROGNOP;
    tok->operands = statements;
    if (DEBUG & DB_MAKEPROGN) {
        printf("makeprogn\n");
        dbugprinttok(tok);
        dbugprinttok(statements);
    };
    return tok;
}

TOKEN makefor(int sign, TOKEN tok, TOKEN asg, TOKEN tokb, TOKEN endexpr, TOKEN tokc,
              TOKEN statement) {
    TOKEN loopstack = NULL;
    TOKEN test, increment, goto_start, if_stmt;
    int start_label = makelabel();

    TOKEN var = asg->operands;  // get loop variable (the LHS of :=)

    // create test
    TOKEN test_op = talloc();
    test_op->tokentype = OPERATOR;
    test_op->whichval = (sign == 1) ? LEOP : GEOP;
    test = binop(test_op, copytok(var), endexpr);

    // create increment
    TOKEN plus_op = talloc();
    plus_op->tokentype = OPERATOR;
    plus_op->whichval = (sign == 1) ? PLUSOP : MINUSOP;

    TOKEN assign_op = talloc();
    assign_op->tokentype = OPERATOR;
    assign_op->whichval = ASSIGNOP;

    increment = binop(assign_op, copytok(var), binop(plus_op, copytok(var), makeintc(1)));

    // assemble body of loop: increment followed by goto to start
    goto_start = makegoto(start_label);
    TOKEN body_progn = makeprogn(tokc, nconc(statement, nconc(increment, goto_start)));

    if_stmt = makeif(tokb, test, body_progn, NULL);  // wrap the body in the if test

    loopstack = nconc(asg, nconc(dolabel(makeintc(start_label), tok, NULL), if_stmt));

    return makeprogn(talloc(), loopstack);
}

TOKEN findid(TOKEN tok) {
    SYMBOL s;
    s = searchst(tok->stringval);  // seach symbol table for the identifier string in token

    if (s == NULL) {
        return tok;  // not found => undeclared variable => return token as is
        // TODO: check if need to return error
    }

    tok->symentry = s;  // attach symbol table entry to token

    tok->symtype = s->datatype;  // attach data type to token

    // handle Constant Identifiers
    // if symbol is a constant, transform token into a number
    if (s->kind == CONSTSYM) {
        tok->tokentype = NUMBERTOK;
        tok->basicdt = s->basicdt;

        if (s->basicdt == INTEGER) {
            tok->intval = s->constval.intnum;
        } else if (s->basicdt == REAL) {
            tok->realval = s->constval.realnum;
        } else if (s->basicdt == STRINGTYPE) {
            strcpy(tok->stringval, s->constval.stringconst);
        }
    }

    return tok;
}

TOKEN findtype(TOKEN tok) {
    SYMBOL s;

    s = searchst(tok->stringval);  // search symbol table for the type name in token

    if (s == NULL) {
        yyerror("Undefined type identifier");
        return tok;
    }

    // ensure that the symbol found is actually a type
    if (s->kind == BASICTYPE || s->kind == TYPESYM) {
        tok->symtype = s;
    } else {
        yyerror("Identifier is not a type name");
    }

    return tok;
}

void yyerror(char const* s) {
    fputs(s, stderr);
    putc('\n', stderr);
}

/* Get the next token; works with peektok. */
TOKEN gettok() {
    TOKEN tok;
    if (savedtoken != NULL) {
        tok = savedtoken;
        savedtoken = NULL;
    } else {
        tok = gettoken();
    }

    if (DEBUG & DB_GETTOK) {
        printf("gettok\n");
        dbugprinttok(tok);
    };

    return (tok);
}

/* Peek at the next token */
TOKEN peektok() {
    if (savedtoken == NULL) {
        savedtoken = gettoken();
    }

    if (DEBUG & DB_GETTOK) {
        printf("peektok\n");
        dbugprinttok(savedtoken);
    };

    return (savedtoken);
}

/* Test for a reserved word */
int reserved(TOKEN tok, int n) {
    return (tok->tokentype == RESERVED && (tok->whichval + RESERVED_BIAS) == n);
}

/* Parse a BEGIN ... END statement */
TOKEN parsebegin(TOKEN keytok) {
    TOKEN front, end, tok;
    TOKEN statement();
    int done;
    front = NULL;
    done = 0;
    while (done == 0) {
        tok = statement(); /* Get a statement */
        if (front == NULL) /* Put at end of list */
            front = tok;
        else
            end->link = tok;
        tok->link = NULL;
        end = tok;
        tok = gettok(); /* Get token: END or semicolon */
        if (reserved(tok, END))
            done = 1;
        else if (tok->tokentype != DELIMITER || (tok->whichval + DELIMITER_BIAS) != SEMICOLON)
            yyerror("Bad item in begin - end.");
    };
    return (makeprogn(keytok, front));
}

/* Parse an IF ... THEN ... ELSE statement */
TOKEN parseif(TOKEN keytok) {
    TOKEN expr, thenpart, elsepart, tok;
    TOKEN parseexpr();
    TOKEN statement();
    expr = parseexpr();
    tok = gettok();
    if (reserved(tok, THEN) == 0) yyerror("Missing THEN");
    thenpart = statement();
    elsepart = NULL;
    tok = peektok();
    if (reserved(tok, ELSE)) {
        tok = gettok(); /* consume the ELSE */
        elsepart = statement();
    };
    return (makeif(keytok, expr, thenpart, elsepart));
}

/* Parse an assignment statement */
TOKEN parseassign(TOKEN lhs) {
    TOKEN tok, rhs;
    TOKEN parseexpr();
    tok = gettok();
    if (tok->tokentype != OPERATOR || tok->whichval != ASSIGNOP) printf("Unrecognized statement\n");
    rhs = parseexpr();
    return (binop(tok, lhs, rhs));
}

/* *opstack and *opndstack allow reduce to manipulate the stacks of parseexpr */
/* Reduce an op and 2 operands */
void reduce(TOKEN* opstack, TOKEN* opndstack) {
    TOKEN op, lhs, rhs;
    if (DEBUG & DB_EXPR) {
        printf("reduce\n");
    };
    op = *opstack; /* pop one operator from op stack */
    *opstack = op->link;
    rhs = *opndstack; /* pop two operands from opnd stack */
    lhs = rhs->link;
    *opndstack = lhs->link;
    *opndstack = cons(binop(op, lhs, rhs), *opndstack); /* push result opnd */
}

/*                             +     *                                     */
static int precedence[] = {0, 1, 0, 3}; /* **** trivial version **** */

/* Parse an expression using operator precedence */
TOKEN parseexpr() {
    /* Partial implementation -- handles +, *, ()    */
    TOKEN tok, op, lhs, rhs;
    int state, done;
    TOKEN opstack, opndstack;
    if (DEBUG & DB_EXPR) {
        printf("parseexpr\n");
    };
    done = 0;
    state = 0;
    opstack = NULL;
    opndstack = NULL;
    while (done == 0) {
        tok = peektok();
        switch (tok->tokentype) {
            case IDENTIFIERTOK:
                tok = gettok();
                tok = findid(tok);  // resolve the identifier immediately
                opndstack = cons(tok, opndstack);
                break;
            case NUMBERTOK: /* operand: push onto stack */
                tok = gettok();
                opndstack = cons(tok, opndstack);
                break;
            case DELIMITER:
                if ((tok->whichval + DELIMITER_BIAS) == LPAREN) {
                    tok = gettok();
                    opstack = cons(tok, opstack);
                } else if ((tok->whichval + DELIMITER_BIAS) == RPAREN) {
                    tok = gettok();
                    while (opstack != NULL && (opstack->tokentype != DELIMITER))
                        reduce(&opstack, &opndstack);
                    opstack = opstack->link; /* discard the left paren */
                } else
                    done = 1;
                break;
            case OPERATOR:
                if (tok->whichval != DOTOP) /* special case for now */
                {
                    tok = gettok();
                    while (opstack != NULL && opstack->tokentype != DELIMITER &&
                           (precedence[opstack->whichval] >= precedence[tok->whichval]))
                        reduce(&opstack, &opndstack);
                    opstack = cons(tok, opstack);
                } else
                    done = 1;
                break;
            default:
                done = 1;
        }
    }
    while (opstack != NULL) reduce(&opstack, &opndstack);
    return (opndstack);
}

void parsevar() {
    TOKEN idlist, typetok, tok;

    // already consumed 'VAR' in the calling function
    while (peektok()->tokentype == IDENTIFIERTOK) {
        idlist = NULL;

        // collect the list of identifiers (i, lim)
        while (1) {
            tok = gettok();
            idlist = nconc(idlist, tok);  // add identifier to list

            tok = peektok();
            if (tok->tokentype == DELIMITER && (tok->whichval + DELIMITER_BIAS) == COMMA) {
                gettok();  // consume comma & keep looping
            } else {
                break;  // no more commas, move on to the colon
            }
        }

        // expect a colon ':'
        tok = gettok();
        if (!(tok->tokentype == DELIMITER && (tok->whichval + DELIMITER_BIAS) == COLON)) {
            yyerror("Missing colon in var declaration");
        }

        typetok = gettok();
        typetok = findtype(typetok);  // resolve 'integer' to its symbol table entry

        instvars(idlist, typetok);  // put variables into symbol table

        // expect a semicolon ';'
        tok = gettok();
        if (!(tok->tokentype == DELIMITER && (tok->whichval + DELIMITER_BIAS) == SEMICOLON)) {
            yyerror("Missing semicolon in var declaration");
        }
    }
}

TOKEN parsefor(TOKEN keytok) {
    TOKEN asg, endexpr, stmt, tok;
    TOKEN tokb, tokc;
    int sign = 1;  // deafult to 'to'

    // parse assignment (i := 0)
    tok = gettok();
    if (tok->tokentype != IDENTIFIERTOK) yyerror("Expected identifier in for loop");

    asg = parseassign(findid(tok));  // resolve 'i' and then parse the assignment

    // epxect 'to' or 'downto'
    tok = gettok();
    if (reserved(tok, TO)) {
        sign = 1;
    } else if (reserved(tok, DOWNTO)) {
        sign = -1;
    } else {
        yyerror("Expected TO or DOWNTO");
    }

    endexpr = parseexpr();

    // expect 'do'
    tokb = gettok();
    if (!reserved(tokb, DO)) {
        yyerror("Missing DO");
    }

    // parse the loop body statement
    tokc = talloc();
    stmt = statement();

    return makefor(sign, keytok, asg, tokb, endexpr, tokc, stmt);  // build the tree with makefor
}

/* Parse a Pascal statement: the "big switch" */
TOKEN statement() {
    TOKEN tok, result;
    result = NULL;
    tok = gettok();
    if (tok->tokentype == RESERVED) {
        /* the big switch */
        switch (tok->whichval + RESERVED_BIAS) {
            case BEGINBEGIN:
                result = parsebegin(tok);
                break;
            case IF:
                result = parseif(tok);
                break;
            case FOR:
                result = parsefor(tok);
                break;
        }
    } else if (tok->tokentype == IDENTIFIERTOK)
        result = parseassign(tok);
    return (result);
}

/* program = statement . */
int yyparse() {
    TOKEN tok;
    TOKEN name;
    TOKEN args;
    TOKEN dottok;
    savedtoken = NULL;

    tok = gettok();

    if (!reserved(tok, PROGRAM)) {
        yyerror("Missing PROGRAM header");
    }

    name = gettok();  // program name (e.g. graph1)
    tok = gettok();   // expect '('

    // simple logic for trivb: consume arguments until ')'
    while (!(tok->tokentype == DELIMITER && (tok->whichval + DELIMITER_BIAS) == RPAREN)) {
        tok = gettok();
    }

    tok = gettok();  // expect ';'

    tok = peektok();
    if (reserved(tok, VAR)) {
        gettok();    // consume 'VAR'
        parsevar();  // handle i, lim : integer;
    }

    parseresult = statement();
    dottok = gettok(); /* get the period at the end */

    if (dottok->tokentype == OPERATOR && dottok->whichval == DOTOP) {
        return (0);
    } else {
        return (1);
    }
}

/* Call yyparse repeatedly to test */
int main(void) {
    int res;
    initscanner();
    init_charclass(); /* initialize character class array */
    printf("Started parser test.\n");
    res = yyparse();
    printf("yyparse result = %8d\n", res);
    if (DEBUG & DB_PARSERES) dbugprinttok(parseresult);
    ppexpr(parseresult);
}
