type 'a sexpr =
  | Atom of 'a
  | List of 'a sexpr list
