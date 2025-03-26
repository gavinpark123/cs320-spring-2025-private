%{
open Utils
%}

%token EOF

%start <string Utils.sexpr> sexpr

%%

sexpr:
  | EOF { List [] }
