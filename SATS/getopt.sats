
(* ****** ****** *)

datatype errcode =
  | ERRmissing_param
  | ERRunknown_argument

(* ****** ****** *)

// option information
typedef optinfo = @{
  lname= string(*long name*)
, sname= char(*short name*)
, required= bool(*true if an argument is required*)
, help= string(*help text*)
}

(* ****** ****** *)

// called when an argument passed from command-line
// matches one of the options passed to [getopt]
fun{}
arg_match (
  optind: size_t(*index into [opts]*)
, &optinfo >> _(*reference to option info*)
, key: string(*argument*)
, value: string(*parameter*)
): void
// called when an error is encountered
fun{}
arg_error (arg: string, index: size_t, errcode): void

datatype
getopt_ret = // return codes
| GOnext of () // try iterating further
| GOstop of () // stop (at end of argument list)
| GOerr of () // error encountered

// the main function
fun{}
getopt {n,n1,m:int | n1 <= n} (
  argc: size_t(n)
, argv: &(@[string][n])
, cur: &size_t(n1) >> size_t(n2)(*current option*)
, opts: &(@[optinfo][m])(*option information*)
, optsz: size_t(m)
): #[n2:int | n2 <= n] getopt_ret

fun{}
unit_test (): void
