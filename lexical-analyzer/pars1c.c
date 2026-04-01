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
#include <string.h>

/* 1. Define TOKEN first and foremost */
#include "token.h"

/* 2. Define the scanner and symbol table headers */
#include "lexan.h"
// #include "symtab.h"

// parse.h after symtab.h because it needs the symbol table definitions
#include "parse.h"

/* 3. Now include the printing headers */
#include "pprint.h"

// #include "codegen.h" here for now

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

/* forward declaration for mutually recursive functions */
TOKEN statement();
TOKEN parseexpr();
TOKEN parsefuncall(TOKEN fn);
void parseconst();
void parsetype();
void parsevar();
TOKEN parsepostfix(TOKEN tok);
TOKEN gettok();
TOKEN peektok();
int reserved(TOKEN tok, int n);
void yyerror(char const* s);

/* Global counter for labels */
int labelnumber = 0;

/* Label Table: maps user label numbers to internal label numbers */
#define MAXLABELS 50
int labeltable[MAXLABELS];    // user label number 
int labelvalues[MAXLABELS];   // internal label number 
int nlabels = 0;

TOKEN makelabel() {
    TOKEN tok = talloc();
    tok->tokentype = NUMBERTOK;
    tok->basicdt = INTEGER;
    tok->intval = labelnumber++;

    return tok;
}

TOKEN makeintc(int num) {
    TOKEN tok = talloc();
    tok->tokentype = NUMBERTOK;
    tok->basicdt = INTEGER;
    tok->intval = num;

    return tok;
}

TOKEN makefuncall(TOKEN tok, TOKEN fn, TOKEN args) {
    if (tok == NULL) tok = talloc();
    tok->tokentype = OPERATOR;
    tok->whichval = FUNCALLOP;
    tok->operands = cons(fn, args);  // link function name to args

    return tok;
}

TOKEN copytok(TOKEN origtok) {
    TOKEN newtok = talloc();
    if (origtok != NULL) *newtok = *origtok;
    newtok->link = NULL;

    return newtok;
}

TOKEN nconc(TOKEN lista, TOKEN listb) {
    TOKEN t;
    if (lista == NULL) return listb;
    t = lista;
    while (t->link != NULL) t = t->link;
    t->link = listb;

    return lista;
}

TOKEN makegoto(int label) {
    TOKEN tok = talloc();
    tok->tokentype = OPERATOR;
    tok->whichval = GOTOOP;
    tok->operands = makeintc(label);

    return tok;
}

TOKEN dolabel(TOKEN labeltok, TOKEN tok, TOKEN statement) {
    if (tok == NULL) tok = talloc();
    tok->tokentype = OPERATOR;
    tok->whichval = LABELOP;
    tok->operands = labeltok;

    return tok;  // in tree format, lanel is just a node in the list
}

/* Install variables into the symbol table */
void instvars(TOKEN idlist, TOKEN typetok) {
    SYMBOL sym;
    TOKEN t;

    for (t = idlist; t != NULL; t = t->link) {
        sym = insertsym(t->stringval);
        sym->kind = VARSYM;
        sym->datatype = typetok->symtype;
        sym->basicdt = sym->datatype->basicdt;

        /* align the offset */
        int align = alignsize(sym->datatype);
        blockoffs[blocknumber] = wordaddress(blockoffs[blocknumber], align);

        sym->offset = blockoffs[blocknumber];
        sym->size = sym->datatype->size;
        blockoffs[blocknumber] += sym->size;
    }
}

/* instlabel installs a user label into the label table */
void instlabel(TOKEN num) {
    if (nlabels >= MAXLABELS) { yyerror("Too many labels"); return; }
    labeltable[nlabels] = num->intval;
    labelvalues[nlabels] = labelnumber++;
    nlabels++;
}

/* wordaddress pads offset n to a multiple of wordsize */
int wordaddress(int n, int wordsize) {
    if (wordsize <= 0) {
        return n;
    }

    return ((n + wordsize - 1) / wordsize) * wordsize;
}

/* makesubrange makes a SUBRANGE symbol table entry */
TOKEN makesubrange(TOKEN tok, int low, int high) {
    SYMBOL sym = symalloc();
    sym->kind = SUBRANGE;
    sym->basicdt = INTEGER;
    sym->lowbound = low;
    sym->highbound = high;
    sym->size = basicsizes[INTEGER];

    tok->symtype = sym;

    return tok;
}

/* instenum installs an enumerated subrange */
TOKEN instenum(TOKEN idlist) {
    int count = 0;
    TOKEN t;
    SYMBOL sym;

    for (t = idlist; t != NULL; t = t->link) {
        sym = insertsym(t->stringval);
        sym->kind = CONSTSYM;
        sym->basicdt = INTEGER;
        sym->constval.intnum = count++;
    }
    TOKEN tok = talloc();
    
    return makesubrange(tok, 0, count - 1);
}

/* instdotdot installs a .. subrange */
TOKEN instdotdot(TOKEN lowtok, TOKEN dottok, TOKEN hightok) {
    return makesubrange(dottok, lowtok->intval, hightok->intval);
}

/* insttype will install a type name in symbol table */
void insttype(TOKEN typename, TOKEN typetok) {
    SYMBOL sym = searchins(typename->stringval);
    sym->kind = TYPESYM;
    sym->datatype = typetok->symtype;
    sym->size = sym->datatype->size;
    sym->basicdt = sym->datatype->basicdt;
}

/* instpoint will install a pointer type in symbol table */
TOKEN instpoint(TOKEN tok, TOKEN typename) {
    SYMBOL sym = symalloc();
    sym->kind = POINTERSYM;
    sym->basicdt = POINTER;
    sym->size = basicsizes[POINTER];
    sym->datatype = searchins(typename->stringval);
    tok->symtype = sym;

    return tok;
}

/* instfields installs type in a list of field name tokens */
TOKEN instfields(TOKEN idlist, TOKEN typetok) {
    TOKEN t;

    for (t = idlist; t != NULL; t = t->link) {
        t->symtype = typetok->symtype;
    }

    return idlist;
}

/* instrec installs a record definition */
TOKEN instrec(TOKEN rectok, TOKEN argstok) {
    SYMBOL rec = symalloc();
    rec->kind = RECORDSYM;

    int offset = 0;
    SYMBOL first = NULL;
    SYMBOL prev = NULL;
    TOKEN t;
    
    for (t = argstok; t != NULL; t = t->link) {
        SYMBOL field = makesym(t->stringval);
        field->datatype = t->symtype;
        field->basicdt = field->datatype->basicdt;

        int align = alignsize(field->datatype);
        offset = wordaddress(offset, align);
        field->offset = offset;
        field->size = field->datatype->size;
        offset += field->size;

        if (first == NULL) first = field;
        if (prev != NULL) prev->link = field;
        prev = field;
    }

    rec->datatype = first;
    rec->size = wordaddress(offset, RECORDALIGN);
    rectok->symtype = rec;

    return rectok;
}

/* instarray installs an array declaration */
TOKEN instarray(TOKEN bounds, TOKEN typetok) {
    SYMBOL arr = symalloc();
    arr->kind = ARRAYSYM;
    SYMBOL sub = bounds->symtype;
    
    arr->lowbound = sub->lowbound;
    arr->highbound = sub->highbound;
    arr->datatype = typetok->symtype;
    arr->size = (sub->highbound - sub->lowbound + 1) * arr->datatype->size;
    
    bounds->symtype = arr;
    
    return bounds;
}

/* settoktype sets up the type fields of a token */
void settoktype(TOKEN tok, SYMBOL typ, SYMBOL ent) {
    tok->symtype = typ;
    if (typ != NULL) tok->basicdt = typ->basicdt;
    tok->symentry = ent;
}

TOKEN fillintc(TOKEN tok, int num) {
    tok->tokentype = NUMBERTOK;
    tok->basicdt = INTEGER;
    tok->intval = num;
    
    return tok;
}

/* makearef makes an array reference operation */
TOKEN makearef(TOKEN var, TOKEN off, TOKEN tok) {
    if (tok == NULL) {
        tok = talloc();
    }

    tok->tokentype = OPERATOR;
    tok->whichval = AREFOP;
    tok->operands = var;
    var->link = off;
    off->link = NULL;

    tok->symtype = var->symtype;
    tok->basicdt = var->basicdt;

    return tok;
}

/* makeplus makes a + operator */
TOKEN makeplus(TOKEN lhs, TOKEN rhs, TOKEN tok) {
    if (tok == NULL) {
        tok = talloc();
    }

    tok->tokentype = OPERATOR;
    tok->whichval = PLUSOP;
    tok->operands = lhs;
    lhs->link = rhs;
    rhs->link = NULL;
    tok->basicdt = INTEGER;
    
    return tok;
}

/* addint adds integer off to expression exp */
TOKEN addint(TOKEN exp, TOKEN off, TOKEN tok) {
    return makeplus(exp, off, tok);
}

/* addoffs adds offset off to an aref expression exp */
TOKEN addoffs(TOKEN exp, TOKEN off) {
    TOKEN offsettok = exp->operands->link;

    if (offsettok->tokentype == NUMBERTOK) {
        offsettok->intval += off->intval;
    } else if (offsettok->tokentype == OPERATOR && offsettok->whichval == PLUSOP) {
        TOKEN firstarg = offsettok->operands;
        if (firstarg->tokentype == NUMBERTOK) {
            firstarg->intval += off->intval;
        }
    }
    
    return exp;
}

/* mulint multiplies expression exp by integer n */
TOKEN mulint(TOKEN exp, int n) {
    TOKEN mult = talloc();
    mult->tokentype = OPERATOR;
    mult->whichval = TIMESOP;
    mult->basicdt = INTEGER;

    TOKEN ntok = makeintc(n);
    mult->operands = ntok;
    ntok->link = exp;
    exp->link = NULL;
    
    return mult;
}

/* reducedot handles a record field reference */
TOKEN reducedot(TOKEN var, TOKEN dot, TOKEN field) {
    SYMBOL recsym = var->symtype;
    if (recsym == NULL) { yyerror("reducedot: null type"); return var; }

    // if type is a TYPESYM, follow to the actual type
    if (recsym->kind == TYPESYM) {
        recsym = recsym->datatype;
    }

    if (recsym->kind != RECORDSYM) {
        yyerror("reducedot: not a record");
        return var;
    }

    // search the field list
    SYMBOL fld = recsym->datatype;
    while (fld != NULL && strcmp(fld->namestring, field->stringval) != 0)
        fld = fld->link;
    if (fld == NULL) { yyerror("Field not found"); return var; }

    TOKEN offtok = makeintc(fld->offset);

    // if var is already an aref, add offset to it
    if (var->tokentype == OPERATOR && var->whichval == AREFOP) {
        addoffs(var, offtok);
        var->symtype = fld->datatype;
        var->basicdt = fld->datatype->basicdt;
        return var;
    }

    // otherwise create a new aref
    TOKEN result = makearef(var, offtok, dot);
    result->symtype = fld->datatype;
    result->basicdt = fld->datatype->basicdt;
    return result;
}

/* arrayref processes an array reference a[i] */
TOKEN arrayref(TOKEN arr, TOKEN tok, TOKEN subs, TOKEN tokb) {
    TOKEN result = arr;
    TOKEN sub = subs;

    while (sub != NULL) {
        TOKEN nextsub = sub->link;
        sub->link = NULL;

        SYMBOL arrsym = result->symtype;
        if (arrsym->kind == TYPESYM) arrsym = arrsym->datatype;
        if (arrsym->kind != ARRAYSYM) { yyerror("arrayref: not an array"); return result; }

        int elemsize = arrsym->datatype->size;
        int low = arrsym->lowbound;

        TOKEN offset;
        if (sub->tokentype == NUMBERTOK && sub->basicdt == INTEGER) {
            // constant subscript: compute offset directly
            int val = (sub->intval - low) * elemsize;
            offset = makeintc(val);
        } else {
            // variable subscript: (+ (-low*elemsize) (* elemsize sub))
            TOKEN negoff = makeintc(-low * elemsize);
            TOKEN scaled = mulint(sub, elemsize);
            offset = makeplus(negoff, scaled, NULL);
        }

        if (result->tokentype == OPERATOR && result->whichval == AREFOP) {
            // already an aref -- adjust
            addoffs(result, offset);
            result->symtype = arrsym->datatype;
            result->basicdt = arrsym->datatype->basicdt;
        } else {
            result = makearef(result, offset, NULL);
            result->symtype = arrsym->datatype;
            result->basicdt = arrsym->datatype->basicdt;
        }
        sub = nextsub;
    }
    return result;
}

/* dopoint handles a ^ pointer dereference */
TOKEN dopoint(TOKEN var, TOKEN tok) {
    tok->tokentype = OPERATOR;
    tok->whichval = POINTEROP;
    tok->operands = var;
    var->link = NULL;

    SYMBOL ptrtype = var->symtype;
    /* Follow through TYPESYM to get actual structure */
    if (ptrtype != NULL && ptrtype->kind == TYPESYM)
        ptrtype = ptrtype->datatype;

    if (ptrtype != NULL && ptrtype->kind == POINTERSYM) {
        SYMBOL target = ptrtype->datatype;
        if (target != NULL && target->kind == TYPESYM) {
            tok->symtype = target->datatype;
        } else {
            tok->symtype = target;
        }
    }
    if (tok->symtype != NULL) {
        tok->basicdt = tok->symtype->basicdt;
    }

    return tok;
}

/* makewhile makes structures for a while statement */
TOKEN makewhile(TOKEN tok, TOKEN expr, TOKEN tokb, TOKEN statement) {
    TOKEN label = makelabel();
    TOKEN labeltok = dolabel(makeintc(label->intval), tok, NULL);

    TOKEN gototok = makegoto(label->intval);

    // explicitly link statement->goto w/o following statement's existing link chain
    statement->link = gototok;
    gototok->link = NULL;
    TOKEN body = makeprogn(tokb, statement);
    TOKEN iftok = makeif(talloc(), expr, body, NULL);

    labeltok->link = iftok;
    iftok->link = NULL;

    return makeprogn(talloc(), labeltok);
}

/* parsepostfix handles ^, ., and [] after an identifier/expression */
TOKEN parsepostfix(TOKEN tok) {
    int done = 0;

    while (!done) {
        TOKEN next = peektok();
        if (next->tokentype == OPERATOR &&
            (next->whichval == POINTEROP || (next->whichval + OPERATOR_BIAS) == POINT)) {
            TOKEN caret = gettok();
            tok = dopoint(tok, caret);
        } else if (next->tokentype == OPERATOR &&
                   (next->whichval == DOTOP || (next->whichval + OPERATOR_BIAS) == DOT)) {
            TOKEN dot = gettok();
            TOKEN field = gettok();
            tok = reducedot(tok, dot, field);
        } else if (next->tokentype == DELIMITER &&
                   (next->whichval + DELIMITER_BIAS) == LBRACKET) {
            TOKEN lbr = gettok();
            TOKEN subs = NULL;
            while (1) {
                TOKEN sub = parseexpr();
                subs = nconc(subs, sub);
                next = peektok();
                if (next->tokentype == DELIMITER &&
                    (next->whichval + DELIMITER_BIAS) == COMMA) {
                    gettok();
                } else break;
            }
            TOKEN rbr = gettok(); // consume ]
            tok = arrayref(tok, lbr, subs, rbr);
        } else {
            done = 1;
        }
    }
    return tok;
}

TOKEN cons(TOKEN item, TOKEN list) {
    item->link = list;

    // if (DEBUG & DB_CONS) {
    //     printf("cons\n");
    //     dbugprinttok(item);
    //     dbugprinttok(list);
    // };

    return item;
}

/* reduce binary operator */
/* operator, left-hand side, right-hand side */
TOKEN binop(TOKEN op, TOKEN lhs, TOKEN rhs) {
    if (lhs != NULL) lhs->link = NULL;
    if (rhs != NULL) rhs->link = NULL;

    // if (DEBUG & DB_BINOP) {
    //     printf("binop\n");
    //     dbugprinttok(op);  /*       op         =  (op lhs rhs)      */
    //     dbugprinttok(lhs); /*      /                                */
    //     dbugprinttok(rhs); /*    lhs --- rhs                        */
    // };

    // only coerce INTEGER<->REAL; skip for POINTER and other types
    if (lhs->basicdt != POINTER && rhs->basicdt != POINTER) {
        if (lhs->basicdt == INTEGER && rhs->basicdt == REAL) {
            TOKEN f = talloc();
            f->tokentype = OPERATOR;
            f->whichval = FLOATOP;
            f->operands = lhs;
            f->basicdt = REAL;
            lhs = f;
        } else if (lhs->basicdt == REAL && rhs->basicdt == INTEGER) {
            TOKEN f = talloc();
            f->tokentype = OPERATOR;
            f->whichval = FLOATOP;
            f->operands = rhs;
            f->basicdt = REAL;
            rhs = f;
        }
    }

    op->operands = lhs;
    lhs->link = rhs;
    op->basicdt = (lhs->basicdt == REAL || rhs->basicdt == REAL) ? REAL : INTEGER;

    return op;
}

TOKEN makeif(TOKEN tok, TOKEN exp, TOKEN thenpart, TOKEN elsepart) {
    tok->tokentype = OPERATOR; /* Make it look like an operator   */
    tok->whichval = IFOP;
    if (elsepart != NULL) elsepart->link = NULL;
    thenpart->link = elsepart;
    exp->link = thenpart;
    tok->operands = exp;

    // if (DEBUG & DB_MAKEIF) {
    //     printf("makeif\n");
    //     dbugprinttok(tok);
    //     dbugprinttok(exp);
    //     dbugprinttok(thenpart);
    //     dbugprinttok(elsepart);
    // };

    return tok;
}

TOKEN makeprogn(TOKEN tok, TOKEN statements) {
    tok->tokentype = OPERATOR;
    tok->whichval = PROGNOP;
    tok->operands = statements;

    // if (DEBUG & DB_MAKEPROGN) {
    //     printf("makeprogn\n");
    //     dbugprinttok(tok);
    //     dbugprinttok(statements);
    // };

    return tok;
}

TOKEN makeprogram(TOKEN name, TOKEN args, TOKEN body) {
    TOKEN tok = talloc();
    tok->tokentype = OPERATOR;
    tok->whichval = PROGRAMOP;
    tok->operands = cons(name, cons(args, body));

    return tok;
}

/* Helper to wrap the args in a progn */
TOKEN makeprogn_args(TOKEN args) {
    TOKEN tok = talloc();
    tok->tokentype = OPERATOR;
    tok->whichval = PROGNOP;
    tok->operands = args;

    return tok;
}

TOKEN makefor(int sign, TOKEN tok, TOKEN asg, TOKEN tokb, TOKEN endexpr, TOKEN tokc,
              TOKEN statement) {
    TOKEN loopstack = NULL;
    TOKEN test, increment, goto_start, if_stmt;
    TOKEN start_label = makelabel();

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
    goto_start = makegoto(start_label->intval);
    TOKEN body_progn = makeprogn(tokc, nconc(statement, nconc(increment, goto_start)));

    if_stmt = makeif(tokb, test, body_progn, NULL);  // wrap the body in the if test

    loopstack = nconc(asg, nconc(dolabel(makeintc(start_label->intval), tok, NULL), if_stmt));

    return makeprogn(talloc(), loopstack);
}

TOKEN findid(TOKEN tok) {
    SYMBOL s;
    s = searchst(tok->stringval);  // seach symbol table for the identifier string in token

    if (s == NULL) {
        return tok;  // not found => undeclared variable => return token as is
    }

    tok->symentry = s;           // attach symbol table entry to token
    tok->symtype = s->datatype;  // attach data type to token
    tok->basicdt = s->basicdt;

    // handle Constant Identifiers
    // if symbol is a constant, transform token into a number
    if (s->kind == CONSTSYM) {
        tok->tokentype = NUMBERTOK;

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

    // if (DEBUG & DB_GETTOK) {
    //     printf("gettok\n");
    //     dbugprinttok(tok);
    // };

    return (tok);
}

/* Peek at the next token */
TOKEN peektok() {
    if (savedtoken == NULL) {
        savedtoken = gettoken();
    }

    // if (DEBUG & DB_GETTOK) {
    //     printf("peektok\n");
    //     dbugprinttok(savedtoken);
    // };

    return (savedtoken);
}

/* Test for a reserved word */
int reserved(TOKEN tok, int n) {
    return (tok->tokentype == RESERVED && (tok->whichval + RESERVED_BIAS) == n);
}

/* Parse a BEGIN ... END statement */
TOKEN parsebegin(TOKEN keytok) {
    TOKEN front = NULL, end = NULL, tok;
    TOKEN statement();
    int done = 0;

    while (done == 0) {
        tok = statement();

        /* Put at end of list */
        if (tok != NULL) {
            if (front == NULL) {
                front = tok;
            } else {
                end->link = tok;
            }
            tok->link = NULL;
            end = tok;
        }

        tok = gettok(); /* Get END or semicolon */
        if (reserved(tok, END)) {
            done = 1;
        } else if (tok->tokentype != DELIMITER || (tok->whichval + DELIMITER_BIAS) != SEMICOLON) {
            yyerror("Bad item in begin - end.");
            printf("Bad item in begin-end! Type: %d, Val: %d, String: '%s'\n", tok->tokentype,
                   tok->whichval, tok->stringval);
        }
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

    tok = gettok();  // consume ':='

    rhs = parseexpr();
    rhs = parsepostfix(rhs);

    /* Coerce integer constant to real if LHS is REAL */
    if (lhs->basicdt == REAL && rhs->basicdt == INTEGER &&
        rhs->tokentype == NUMBERTOK) {
        rhs->basicdt = REAL;
        rhs->realval = (double)rhs->intval;
    }

    if (lhs->basicdt == INTEGER && rhs->basicdt == REAL) {
        TOKEN f = talloc();
        f->tokentype = OPERATOR;
        f->whichval = FIXOP;
        f->operands = rhs;
        f->basicdt = INTEGER;
        rhs = f;
    }

    return (binop(tok, lhs, rhs));
}

/* *opstack and *opndstack allow reduce to manipulate the stacks of parseexpr */
/* Reduce an op and 2 operands */
void reduce(TOKEN* opstack, TOKEN* opndstack) {
    TOKEN op, lhs, rhs;

    if (*opstack == NULL) {
        return;
    }

    op = *opstack;
    *opstack = op->link;

    // handle Unary Minus or NOT
    if (op->symtype == (SYMBOL)1 || op->whichval == NOTOP ||
        (op->whichval + OPERATOR_BIAS) == NOTOP) {
        if (op->symtype == (SYMBOL)1) {
            op->whichval = 2;
        }

        rhs = *opndstack;
        if (rhs != NULL) {
            *opndstack = rhs->link;
            rhs->link = NULL;
            op->basicdt = rhs->basicdt;
        }
        op->operands = rhs;
        *opndstack = cons(op, *opndstack);
    } else {
        // binary operator logic
        rhs = *opndstack;
        if (rhs != NULL) {
            lhs = rhs->link;
            if (lhs != NULL) {
                *opndstack = lhs->link;
                *opndstack = cons(binop(op, lhs, rhs), *opndstack);
            }
        }
    }
}

/*                             +     *                                     */
/* Precedence table for Pascal operators */
static int precedence[] = {
    0,  // dummy
    1,  // +
    1,  // -
    2,  // *
    2,  // /
    2,  // div
    2,  // mod
    0,  // =
    0,  // <>
    0,  // <
    0,  // <=
    0,  // >=
    0,  // >
    1,  // or
    2,  // and
    3   // not
};

/* Parse an expression using operator precedence */
TOKEN parseexpr() {
    /* Partial implementation -- handles +, *, ()    */
    TOKEN tok, op, lhs, rhs;
    int state, done;
    TOKEN opstack, opndstack;

    // if (DEBUG & DB_EXPR) {
    //     printf("parseexpr\n");
    // };

    done = 0;
    state = 0;
    opstack = NULL;
    opndstack = NULL;
    while (done == 0) {
        tok = peektok();
        switch (tok->tokentype) {
            case IDENTIFIERTOK:
                tok = gettok();
                tok = findid(tok);

                if (peektok()->tokentype == DELIMITER &&
                    (peektok()->whichval + DELIMITER_BIAS) == LPAREN) {
                    tok = parsefuncall(tok);
                }
                tok = parsepostfix(tok);
                opndstack = cons(tok, opndstack);

                state = 1;
                break;
            case NUMBERTOK:
                tok = gettok();
                opndstack = cons(tok, opndstack);
                state = 1;
                break;
            case STRINGTOK:
                tok = gettok();
                opndstack = cons(tok, opndstack);
                state = 1;
                break;
            case DELIMITER:
                if ((tok->whichval + DELIMITER_BIAS) == LPAREN) {
                    tok = gettok();
                    opstack = cons(tok, opstack);
                } else if ((tok->whichval + DELIMITER_BIAS) == RPAREN) {
                    int has_lparen = 0;
                    TOKEN temp = opstack;
                    while (temp != NULL) {
                        if (temp->tokentype == DELIMITER &&
                            (temp->whichval + DELIMITER_BIAS) == LPAREN) {
                            has_lparen = 1;
                            break;
                        }
                        temp = temp->link;
                    }

                    if (has_lparen) {
                        tok = gettok();  // consume ')'
                        while (opstack != NULL && opstack->tokentype != DELIMITER)
                            reduce(&opstack, &opndstack);
                        opstack = opstack->link;  // discard '('
                        state = 1;
                    } else {
                        done = 1;
                    }
                } else {
                    done = 1;
                }
                break;
            case OPERATOR:
                if (tok->whichval != DOTOP && (tok->whichval + OPERATOR_BIAS) != DOTOP
                    && tok->whichval != POINTEROP && (tok->whichval + OPERATOR_BIAS) != POINT) {
                    tok = gettok();

                    if (state == 0 &&
                        (tok->whichval == MINUSOP || tok->whichval + OPERATOR_BIAS == MINUSOP ||
                         tok->whichval == 2)) {
                        tok->whichval = 15;
                        tok->symtype = (SYMBOL)1;  // mark as unary
                    }

                    while (opstack != NULL && opstack->tokentype != DELIMITER &&
                           (precedence[opstack->whichval] >= precedence[tok->whichval])) {
                        reduce(&opstack, &opndstack);
                    }
                    opstack = cons(tok, opstack);
                    state = 0;
                } else {
                    done = 1;
                }
                break;
            case RESERVED:
                if (reserved(tok, NIL)) {
                    tok = gettok();
                    tok->tokentype = NUMBERTOK;
                    tok->basicdt = POINTER;
                    tok->intval = 0;
                    opndstack = cons(tok, opndstack);
                    state = 1;
                } else {
                    done = 1;
                }
                break;
            default:
                done = 1;
        }
    }

    while (opstack != NULL) {
        reduce(&opstack, &opndstack);
    }

    return (opndstack);
}

void parseconst() {
    TOKEN id, val, tok;
    SYMBOL s;

    while (peektok()->tokentype == IDENTIFIERTOK) {
        id = gettok();

        // operate on '='
        tok = gettok();
        if (!(tok->tokentype == OPERATOR && tok->whichval + OPERATOR_BIAS == EQ)) {
            yyerror("Expected '=' in const");
        }

        // operate on constant or identifier
        val = gettok();
        if (val->tokentype == IDENTIFIERTOK) {
            val = findid(val);
        }

        // install into symbol table
        s = insertsym(id->stringval);
        s->kind = CONSTSYM;
        s->basicdt = val->basicdt;

        if (val->basicdt == INTEGER) {
            s->constval.intnum = val->intval;
        } else {
            s->constval.realnum = val->realval;
        }

        // expect a semicolon ';'
        tok = gettok();
        if (!(tok->tokentype == DELIMITER && (tok->whichval + DELIMITER_BIAS) == SEMICOLON)) {
            yyerror("Expected ; after constant");
        }
    }
}

/* Helper to create a NOT operator node */
TOKEN make_not(TOKEN exp) {
    TOKEN tok = talloc();
    tok->tokentype = OPERATOR;
    tok->whichval = NOTOP;
    tok->operands = exp;
    return tok;
}

TOKEN parserepeat(TOKEN keytok) {
    TOKEN body = NULL;
    TOKEN cond;
    TOKEN result;
    TOKEN top_label = makelabel();

    // parse the body
    while (!reserved(peektok(), UNTIL)) {
        body = nconc(body, statement());
        if (peektok()->tokentype == DELIMITER &&
            (peektok()->whichval + DELIMITER_BIAS) == SEMICOLON) {
            gettok();
        }
    }

    gettok();            // consume UNTIL
    cond = parseexpr();  // parse the exit condition (n = 0)

    // build the tree: (progn (label top) body (if (not cond) (goto top)))
    TOKEN jump_back =
        makeif(talloc(), cond, makeprogn(talloc(), NULL), makegoto(top_label->intval));
    TOKEN label_node = dolabel(makeintc(top_label->intval), talloc(), NULL);

    return makeprogn(keytok, nconc(label_node, nconc(body, jump_back)));
}

/* parsetype_desc parses a type description and returns a token with symtype set */
TOKEN parsetype_desc() {
    TOKEN tok = peektok();

    // enum: (red, white, blue)
    if (tok->tokentype == DELIMITER && (tok->whichval + DELIMITER_BIAS) == LPAREN) {
        gettok(); // consume (
        TOKEN idlist = NULL;
        while (1) {
            TOKEN id = gettok();
            idlist = nconc(idlist, id);
            if (peektok()->tokentype == DELIMITER &&
                (peektok()->whichval + DELIMITER_BIAS) == COMMA)
                gettok();
            else break;
        }
        gettok(); // consume )
        
        return instenum(idlist);
    }

    // pointer: ^ typename
    if (tok->tokentype == OPERATOR &&
        (tok->whichval == POINTEROP || (tok->whichval + OPERATOR_BIAS) == POINT)) {
        gettok(); // consume ^
        TOKEN tname = gettok();
        
        return instpoint(talloc(), tname);
    }

    // record: record ... end 
    if (reserved(tok, RECORD)) {
        gettok(); // consume RECORD
        TOKEN fields = NULL;
        while (!reserved(peektok(), END)) {
            // parse one field group: id, id, ... : type
            TOKEN idlist = NULL;
            while (1) {
                TOKEN id = gettok();
                idlist = nconc(idlist, id);
                if (peektok()->tokentype == DELIMITER &&
                    (peektok()->whichval + DELIMITER_BIAS) == COMMA)
                    gettok();
                else break;
            }
            tok = gettok(); // consume :
            TOKEN ftype = parsetype_desc();
            instfields(idlist, ftype);
            fields = nconc(fields, idlist);
            // consume optional ;
            if (peektok()->tokentype == DELIMITER &&
                (peektok()->whichval + DELIMITER_BIAS) == SEMICOLON)
                gettok();
        }
        gettok(); // consume END 
        
        return instrec(talloc(), fields);
    }

    // array: array[bounds] of type
    if (reserved(tok, ARRAY)) {
        gettok(); // consume ARRAY
        gettok(); // consume [ 
        // parse bounds list
        TOKEN boundslist = NULL;
        TOKEN boundstail = NULL;
        while (1) {
            TOKEN btok;
            TOKEN first = gettok();
            if (first->tokentype == NUMBERTOK) {
                // number .. number
                TOKEN dottok = gettok(); // consume ..
                TOKEN high = gettok();
                btok = instdotdot(first, dottok, high);
            } else {
                // type name used as range (e.g. color)
                btok = findtype(first);
                // follow to get the subrange
                SYMBOL s = btok->symtype;
                if (s->kind == TYPESYM) s = s->datatype;
                btok->symtype = s;
            }
            if (boundslist == NULL) boundslist = btok;
            else boundstail->link = btok;
            boundstail = btok;
            btok->link = NULL;

            if (peektok()->tokentype == DELIMITER &&
                (peektok()->whichval + DELIMITER_BIAS) == COMMA)
                gettok();
            else break;
        }
        gettok(); // consume " ] "
        gettok(); // consume " OF "
        TOKEN elemtype = parsetype_desc();

        // build arrays from right to left (innermost first)
        // reverse the bounds list
        TOKEN rev = NULL;
        TOKEN cur = boundslist;
        while (cur != NULL) {
            TOKEN next = cur->link;
            cur->link = rev;
            rev = cur;
            cur = next;
        }

        // now rev is the reversed list; apply instarray from front
        TOKEN b = rev;
        while (b != NULL) {
            TOKEN nextb = b->link;
            b->link = NULL;
            elemtype = instarray(b, elemtype);
            b = nextb;
        }
        
        return elemtype;
    }

    // named type: integer, real, complex, pp, etc.
    tok = gettok();
    
    return findtype(tok);
}

/* parsetype parses a type declaration block */
void parsetype() {
    TOKEN tok;
    while (peektok()->tokentype == IDENTIFIERTOK) {
        TOKEN tname = gettok(); // type name
        tok = gettok(); // consume "="
        TOKEN typetok = parsetype_desc();
        insttype(tname, typetok);
        // consume ";"
        if (peektok()->tokentype == DELIMITER &&
            (peektok()->whichval + DELIMITER_BIAS) == SEMICOLON)
            gettok();
    }
}

void parsevar() {
    TOKEN idlist, typetok, tok;

    while (peektok()->tokentype == IDENTIFIERTOK) {
        idlist = NULL;

        while (1) {
            tok = gettok();
            idlist = nconc(idlist, tok);

            tok = peektok();
            if (tok->tokentype == DELIMITER && (tok->whichval + DELIMITER_BIAS) == COMMA) {
                gettok();
            } else {
                break;
            }
        }

        // expect a colon ':'
        tok = gettok();
        if (!(tok->tokentype == DELIMITER && (tok->whichval + DELIMITER_BIAS) == COLON)) {
            yyerror("Missing colon in var declaration");
        }

        typetok = parsetype_desc();
        instvars(idlist, typetok);

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

TOKEN parsefuncall(TOKEN fn) {
    TOKEN args = NULL;
    TOKEN tok = peektok();

    if (tok->tokentype == DELIMITER && (tok->whichval + DELIMITER_BIAS) == LPAREN) {
        gettok(); // consume "("

        while (1) {
            if (peektok()->tokentype == STRINGTOK) {
                args = nconc(args, gettok());
            } else {
                TOKEN arg = parseexpr();
                arg = parsepostfix(arg);
                args = nconc(args, arg);
            }

            tok = peektok();
            if (tok->tokentype == DELIMITER && (tok->whichval + DELIMITER_BIAS) == COMMA) {
                gettok();
            } else {
                break;
            }
        }

        tok = gettok(); // consume ")"
                if ((tok->whichval + DELIMITER_BIAS) != RPAREN) {
            yyerror("Missing ')' in function call");
        }
    }

    // new(ptr) → (:= ptr (funcall new size))
    if (strcmp(fn->stringval, "new") == 0 && args != NULL) {
        TOKEN ptrvar = args;
        SYMBOL ptrtype = ptrvar->symtype;
        /* Follow TYPESYM to get the actual POINTERSYM */
        if (ptrtype != NULL && ptrtype->kind == TYPESYM)
            ptrtype = ptrtype->datatype;
        int size = 0;
        
        if (ptrtype != NULL && ptrtype->kind == POINTERSYM) {
            SYMBOL target = ptrtype->datatype;
            if (target != NULL && target->kind == TYPESYM)
                size = target->datatype->size;
            else if (target != NULL)
                size = target->size;
        }
        
        TOKEN sizearg = makeintc(size);
        TOKEN funcall = makefuncall(NULL, fn, sizearg);
        TOKEN assignop = talloc();

        assignop->tokentype = OPERATOR;
        assignop->whichval = ASSIGNOP;
        assignop->operands = ptrvar;
        ptrvar->link = funcall;
        funcall->link = NULL;

        return assignop;
    }

    // writeln/write type dispatch (skip for string arguments)
    if (args != NULL && args->tokentype != STRINGTOK) {
        if (strcmp(fn->stringval, "writeln") == 0) {
            if (args->basicdt == INTEGER)
                strcpy(fn->stringval, "writelni");
            else if (args->basicdt == REAL)
                strcpy(fn->stringval, "writelnf");
        } else if (strcmp(fn->stringval, "write") == 0) {
            if (args->basicdt == INTEGER)
                strcpy(fn->stringval, "writei");
            else if (args->basicdt == REAL)
                strcpy(fn->stringval, "writef");
        }
    }

    TOKEN result = makefuncall(NULL, fn, args);
    result->basicdt = fn->basicdt;

    return result;
}

/* Parse a Pascal statement: the "big switch" */
TOKEN statement() {
    TOKEN tok, result;
    result = NULL;
    tok = gettok();
    if (tok->tokentype == RESERVED) {
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
            case REPEAT:
                result = parserepeat(tok);
                break;
            case WHILE: {
                TOKEN expr = parseexpr();
                TOKEN dotok = gettok(); // consume DO
                TOKEN stmt = statement();
                result = makewhile(tok, expr, dotok, stmt);
                break;
            }
            case GOTO: {
                TOKEN labnum = gettok();
                int i;
                for (i = 0; i < nlabels; i++) {
                    if (labeltable[i] == labnum->intval) {
                        result = makegoto(labelvalues[i]);
                        break;
                    }
                }
                break;
            }
        }
    } else if (tok->tokentype == NUMBERTOK) {
        // user label: 1492: statement
        TOKEN colon = gettok(); // consume ":"
        int i;
        int internal = -1;
        for (i = 0; i < nlabels; i++) {
            if (labeltable[i] == tok->intval) {
                internal = labelvalues[i];
                break;
            }
        }
        TOKEN labelnode = dolabel(makeintc(internal), colon, NULL);
        TOKEN stmt = statement();
        result = makeprogn(talloc(), nconc(labelnode, stmt));
    } else if (tok->tokentype == IDENTIFIERTOK) {
        tok = findid(tok);
        if (tok->symentry != NULL && tok->symentry->kind == FUNCTIONSYM) {
            result = parsefuncall(tok);
        } else {
            tok = parsepostfix(tok);
            TOKEN next = peektok();
            if (next->tokentype == OPERATOR &&
                (next->whichval == ASSIGNOP || next->whichval + OPERATOR_BIAS == ASSIGNOP)) {
                result = parseassign(tok);
            } else {
                result = parsefuncall(tok);
            }
        }
    }

    return (result);
}

/* program = statement . */
int yyparse() {
    TOKEN tok;
    TOKEN name;
    TOKEN args;
    TOKEN body;

    TOKEN arg_list = NULL;
    savedtoken = NULL;

    tok = gettok();
    if (!reserved(tok, PROGRAM)) {
        yyerror("Missing PROGRAM header");
    }

    name = gettok();  // program name (e.g. graph1)
    if (name->tokentype != IDENTIFIERTOK) {
        yyerror("Expected program name");
    }

    tok = gettok();  // expect '('
    if (tok->tokentype == DELIMITER && tok->whichval + DELIMITER_BIAS == LPAREN) {
        tok = gettok();
        while (!((tok->tokentype == DELIMITER) && (tok->whichval + DELIMITER_BIAS) == RPAREN)) {
            arg_list = nconc(arg_list, tok);

            tok = gettok();
            if ((tok->tokentype == DELIMITER) && (tok->whichval + DELIMITER_BIAS) == COMMA) {
                tok = gettok();  // skip comma
            }
        }
    } else {
        yyerror("Expected '(' after program name");
    }

    tok = gettok();  // consume ';'
    if (!((tok->tokentype == DELIMITER) && (tok->whichval + DELIMITER_BIAS) == SEMICOLON)) {
        yyerror("Expected ';' after program header");
    }

    // label block: label 1492, 1776
    tok = peektok();
    if (reserved(tok, LABEL)) {
        gettok(); // consume LABEL
        int userlabels[MAXLABELS];
        int numlabels = 0;
        while (1) {
            TOKEN num = gettok();
            userlabels[numlabels++] = num->intval;
            tok = peektok();
            if (tok->tokentype == DELIMITER && (tok->whichval + DELIMITER_BIAS) == COMMA)
                gettok();
            else break;
        }
        tok = gettok(); // consume ;
        
        // install in reverse order
        for (int li = numlabels - 1; li >= 0; li--) {
            TOKEN ltok = makeintc(userlabels[li]);
            instlabel(ltok);
        }
    }

    tok = peektok();
    if (reserved(tok, CONST)) {
        gettok();
        parseconst();
    }

    // type block
    tok = peektok();
    if (reserved(tok, TYPE)) {
        gettok();
        parsetype();
    }

    tok = peektok();
    if (reserved(tok, VAR)) {
        gettok();
        parsevar();
    }

    body = statement();

    tok = gettok();  // consume ending period
    if (tok == NULL || tok->tokentype != OPERATOR || tok->whichval != DOTOP) {
        yyerror("Expected . at end of program");
    }

    args = makeprogn_args(arg_list);

    parseresult = makeprogram(name, args, body);  // build final tree node

    return 0;  // success
}

/* Call yyparse repeatedly to test */
int main(void) {
    int res;

    initscanner();
    init_charclass(); /* initialize character class array */
    initsyms();       // initialize "integer", "real", etc.

    // printf("Started parser test.\n");
    res = yyparse();  // run parser

    printf("yyparse result = %8d\n", res);

    printstlevel(1);

    // if (DEBUG & DB_PARSERES) {
    //     dbugprinttok(parseresult);
    // }

    ppexpr(parseresult);

    return 0;
}
