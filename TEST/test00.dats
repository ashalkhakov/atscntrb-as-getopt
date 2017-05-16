#include
"share/atspre_staload.hats"

(* ****** ****** *)

staload "libats/SATS/dynarray.sats"
staload _(*anon*) = "libats/DATS/dynarray.dats"
//
#include "./../mylibies.hats"
//
#staload $GETOPT // opening it
//
#include "./../mylibies_link.hats"
//
(* ****** ****** *)
//
typedef testE = @{i=size_t, k=string, v=string}
//
fun
fprint_testE (out: FILEref, e: testE): void =
   fprint!(out, "i=[", e.i, "], k = [", e.k, "], v = [", e.v, "]")
//
implement
fprint_val<testE> (out, e) = fprint_testE (out, e)
//
(* ****** ****** *)
//
implement
main0 () = let
  var lst = dynarray_make_nil<testE>((i2sz)10)
  prval pf_lst = view@ lst
  var count: size_t
  val () = count := g0ofg1 ((i2sz)0)
  prval pf_count = view@ count
//
  implement
  arg_match<> (index, oi, key, value) = let
    prval (pf_lst, fpf) = decode($vcopyenv_v(pf_lst))
    prval (pf_count, fpf_count) = decode($vcopyenv_v(pf_count))
    val () = dynarray_insert_at_exn<testE> (lst, count, @{i= index, k= oi.lname, v= value})
    val () = count := succ(count)
    prval () = fpf (pf_lst)
    prval () = fpf_count (pf_count)
  in
  end
//
  implement
  arg_error<> (arg, ix, ecode) = println!("got error; argument [", arg, "], index = ", ix)
//
  #define NOPTS 3
  var opts = @[optinfo](@{lname="output", sname='o', required=true, help="specify the output file"}, @{lname="warning", sname='W', required=true, help="warning level"}, @{lname="help", sname='h', required=false, help="display help"})
//
  var args0 = @[string]("--output=out.ppm", "--help", "-ofoo.bar", "-o", "baz.qux", "--warning", "WARN", "test arg")
  var cur: size_t
  val () = cur := (i2sz)0
  val-GOnext() = getopt ((i2sz)8, args0, cur, opts, (i2sz)NOPTS)
  val-GOnext() = getopt ((i2sz)8, args0, cur, opts, (i2sz)NOPTS)
  val-GOnext() = getopt ((i2sz)8, args0, cur, opts, (i2sz)NOPTS)
  val-GOnext() = getopt ((i2sz)8, args0, cur, opts, (i2sz)NOPTS)
  val-GOnext() = getopt ((i2sz)8, args0, cur, opts, (i2sz)NOPTS)
  val-GOstop() = getopt ((i2sz)8, args0, cur, opts, (i2sz)NOPTS)
//
  prval () = view@ (lst) := pf_lst
  prval () = view@ (count) := pf_count
  val out = stdout_ref
  val () = fprint_dynarray (out, lst)
  val () = fprintln!(out)
//
  val- @{i= _(*0*), k="output", v="out.ppm"} = dynarray_takeout_at_exn (lst, (i2sz)0)
  val- @{i= _(*2*), k="help", v=_} = dynarray_takeout_at_exn (lst, (i2sz)0)
  val- @{i= _(*0*), k="output", v="foo.bar"} = dynarray_takeout_at_exn (lst, (i2sz)0)
  val- @{i= _(*0*), k="output", v="baz.qux"} = dynarray_takeout_at_exn (lst, (i2sz)0)
  val- @{i= _(*1*), k="warning", v="WARN"} = dynarray_takeout_at_exn (lst, (i2sz)0)
// 
  val-true = (cur = (i2sz)7)
//
  val () = dynarray_free (lst)
//
in
end
