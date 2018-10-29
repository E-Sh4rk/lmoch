
open Translation

type check_result = True | False | Unknown | Error of string

let check ft main_node =
  Unknown
