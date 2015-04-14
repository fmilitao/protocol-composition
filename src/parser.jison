// Copyright (C) 2013-2015 Filipe Militao <filipe.militao@cs.cmu.edu>
// GPL v3 Licensed http://www.gnu.org/licenses/

/* lexical grammar */
%lex

%%

\s+                   /* skip whitespace */
\/\/.*                /* skip comments */
"/*"(.|\n|\r)*?"*/"   /* skip multiline comments */
"int"                 return 'INT_TYPE'
"boolean"             return 'BOOLEAN_TYPE'
"string"              return 'STRING_TYPE'
"share"               return 'SHARE'
"subtype"             return 'SUBTYPE'
"equals"              return 'EQUALS'
"as"                  return 'AS'
"typedef"             return 'TYPEDEF'
"none"                return 'NONE'
"top"                 return 'TOP'
"not"                 return 'NOT'
"(+)"                 return '(+)'
"&"                   return '&'
"||"                  return '||'
"#"                   return '#'
"("                   return '('
")"                   return ')'
"<:"                  return '<:'
"<"                   return '<'
">"                   return '>'
"+"                   return '+'
"*"                   return '*'
"."                   return '.'
","                   return ','
";"                   return ';'
"::"                  return '::'
":"                   return ':'
"=>"                  return '=>'
"=="                  return '=='
"="                   return '='
"!"                   return '!'
"["                   return '['
"]"                   return ']'
"{"                   return '{'
"}"                   return '}'
"/"                   return '/'
"-o"                  return '-o'
"rw"                  return 'RW'
"ref"                 return 'REF'
"exists"              return 'EXISTS'
"forall"              return 'FORALL'
[a-zA-Z0-9_]+         return 'IDENTIFIER'
<<EOF>>               return 'EOF'
/lex

/* operator associations and precedence */

%left '-o' '#'
%left '+'
%right '=>' ';'
%left FORALL EXISTS
%left '{'
%right '::'
%left '*' '(+)' '&'
%left '!' RW
%left ','

%start file

%% /* language grammar */

file
	: EOF
		{ return new AST.Exp.Program(null,[],@$); }
	| program EOF
		{ return $1; }
	;

// TYPES

t
	: NONE
		{ $$ = new AST.Type.None(@$); }
	| TOP
		{ $$ = new AST.Type.Top(@$); }
	| INT_TYPE
	 	{ $$ = new AST.Type.Primitive(yytext,@$); }
	| BOOLEAN_TYPE
	 	{ $$ = new AST.Type.Primitive(yytext,@$); }
	| STRING_TYPE
	 	{ $$ = new AST.Type.Primitive(yytext,@$); }

	| '!' t
 	  	{ $$ = new AST.Type.Bang($2,@$); }
	| id
	 	{ $$ = $1; }
	| REF IDENTIFIER
	 	{ $$ = new AST.Type.Reference($2,@$); }
	| '(' t ')'
	 	{ $$ = $2; }
	| RW IDENTIFIER t
		{ $$ = new AST.Type.Capability($2,$3,@$); }

	| '[' ']'
	 	{ $$ = new AST.Type.Record([],@$); }
	| '[' field_types ']'
	 	{ $$ = new AST.Type.Record($2,@$); }
	| '[' type_list ']'
		{ $$ = new AST.Type.Tuple($2,@$); }

	| FORALL IDENTIFIER '.' t
		{ $$ = new AST.Type.Forall($2,$4,null,@$); }
	| FORALL IDENTIFIER '<:' t '.' t
		{ $$ = new AST.Type.Forall($2,$6,$4,@$); }
	| EXISTS IDENTIFIER '.' t
		{ $$ = new AST.Type.Exists($2,$4,null,@$); }
	| EXISTS IDENTIFIER '<:' t '.' t
		{ $$ = new AST.Type.Exists($2,$6,$4,@$); }

	| t '{' t '/' id '}'
		{ $$ = new AST.Type.Substitution($1,$3,$5,@$); }

	| sum_type
		{ $$ = new AST.Type.Sum($1,@$); }

	| t '=>' t
		{ $$ = new AST.Type.Rely($1,$3,@$); }
	| t ';' t
		{ $$ = new AST.Type.Guarantee($1,$3,@$); }

	| t '-o' t
		{ $$ = new AST.Type.Function($1,$3,@$); }
	| IDENTIFIER '[' type_list ']'
		{ $$ = new AST.Type.Definition($1,$3,@$); }

	| t '::' t
		{ $$ = new AST.Type.Stacked($1,$3,@$); }

	// these collapse their arguments for convenience
	| t '*' t
		{ $$ = new AST.Type.Star($1,$3,@$); }
	| t '&' t
		{ $$ = new AST.Type.Intersection($1,$3,@$); }
	| t '(+)' t
		{ $$ = new AST.Type.Alternative($1,$3,@$); }
	;

// AUX

sum_type
	: IDENTIFIER '#' t
		{ $$ = [new AST.Type.Tagged($1,$3,@$)]; }
	| IDENTIFIER '#' t '+' sum_type
		{ $$ = [new AST.Type.Tagged($1,$3,@$)].concat($5); }
	;

type_list
	: t
		{ $$ = [$1]; }
	| type_list ',' t
		{ $1.push($3); $$ = $1; }
	;

id :
	IDENTIFIER
	 	{ $$ = new AST.Type.Name(yytext,@$); }
	;

field_type :
	IDENTIFIER ':' t
		{ $$ = new AST.Type.Field($1,$3,@$); }
	;

field_types
	: field_type
		{ $$ = [$1]; }
	| field_type ',' field_types
		{ $$ = [$1].concat($3); }
	;

// PROGRAM

program
	: sequence
	  	{ $$ = new AST.Exp.Program(null,$1,@$); }
	| sequence blocks
		{ $$ = new AST.Exp.Program($2.typedefs,$1.concat($2.exp),@$); }
	| blocks
		{ $$ = $1; }
	;

blocks :
	  typedefs sequence
		{ $$ = new AST.Exp.Program($1,$2,@$); }
	| typedefs sequence blocks
		{ $$ = new AST.Exp.Program($1.concat($3.typedefs),$2.concat($3.exp),@$); }
	;

typedefs
	: typedef
		{ $$ = [$1]; }
	| typedef typedefs
		{ $$ = [$1].concat($2); }
	;

typedef
	: TYPEDEF IDENTIFIER '=' t
		{ $$ = new AST.Exp.TypeDef($2,$4,null,@$); }
	| TYPEDEF IDENTIFIER '[' ids_list ']' '=' t
		{ $$ = new AST.Exp.TypeDef($2,$7,$4,@$); }
	;

ids_list
	: IDENTIFIER
		{ $$ = [$1]; }
	| ids_list ',' ids_list
		{ $$ = $1.concat($3); }
	;

sequence
	: forall
		{ $$ = $1; }
	| forall sequence
		{ $$ = $1.concat($2); }
	;

forall
	: '<' IDENTIFIER '>' forall
		{ $$ = [new AST.Exp.Forall($2,$4[0],null,@$)]; }
	| '<' IDENTIFIER '<:' t '>' forall
		{ $$ = [new AST.Exp.Forall($2,$6[0],$4,@$)]; }
    | share
		{ $$ = $1; }
	| subtype
		{ $$ = $1; }
	| equals
		{ $$ = $1; }
	;

share
	: SHARE t AS t '||' t
		{ $$ = [new AST.Exp.Share(true,$2,$4,$6,@$)]; }
	| NOT SHARE t AS t '||' t
		{ $$ = [new AST.Exp.Share(false,$3,$5,$7,@$)]; }
	;

subtype
	: SUBTYPE t '<:' t
		{ $$ = [new AST.Exp.Subtype(true,$2,$4,@$)]; }
	| NOT SUBTYPE t '<:' t
		{ $$ = [new AST.Exp.Subtype(false,$3,$5,@$)]; }
	;

equals
	: EQUALS t '==' t
		{ $$ = [new AST.Exp.Equals(true,$2,$4,@$)]; }
	| NOT EQUALS t '==' t
		{ $$ = [new AST.Exp.Equals(false,$3,$5,@$)]; }
	;
