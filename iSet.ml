(*
 * ISet - Interval sets
 * Copyright (C) 1996-2019 Xavier Leroy, Nicolas Cannasse, Markus Mottl,
   Jacek Chrzaszcz
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version,
 * with the special exception on linking described in file LICENSE.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 *)

(* Interval Set.

    This is an interval set, i.e. a set of integers, where large
    intervals can be stored as single elements. Intervals stored in the
    set are disjoint. 

*)

(* Sety podawane jako argumenty funkcji sa zrownowazone *)

(* TYP *)
(* Empty reprezentuje pusty set *)
(* Node (wierzcholek) zawiera informacje o lewym poddrzewie,
przedziale, który reprezentuje
dany wierzcholek w secie, prawe poddrzewo, wysokosc
(najdluzsza sciezke z tego
wierzcholka do jakiegos liscia), oraz rozmiar
seta reprezentowanego przez ten
wierzcholek (ilosc wierzcholkow w poddrzewach + on sam) *)
type t =
  | Empty
  | Node of t * (int * int) * t * int * int


(* Funckja tworzaca pusty set *)
let empty = Empty


(* Funkcja sprawdzajaca, czy set jest pusty *)
let is_empty s = s = Empty


(* Funkcja sprawdzajaca rozmiar seta *)
let size s =
  match s with
  | Node (_, _, _, _, s) -> s
  | Empty -> 0


(* Funkcja zwracajaca wysokosc seta *)
let height s =
  match s with
  | Node (_, _, _, h, _) -> h
  | Empty -> 0


(* Funkcja zwracajaca najmniejszy element w secie *)
let rec min_elt = function
  | Node (Empty, k, _, _, _) -> k
  | Node (l, _, _, _, _) -> min_elt l
  | Empty -> assert false


(* Funkcja dodajaca do siebie 2 liczby *)
(* Jeżeli suma x i y > max_int, wtedy zwraca max_int *)
let sum x y =
  if max_int - y >= x then x + y
  else max_int


(* Funkcja zwracajaca wielkosc przedzialu
(ilosc liczb naturalnych w przedziale [a, b]) *)
(* Jeżeli wielkosc przedzialu > max_int, wtedy zwraca max_int *)
let interval k =
  let (a, b) = k in 
  let diff = b - a + 1 in
  if diff <= 0 then max_int
  else diff


(* Funkcja tworzaca set *)
(* l - lewe poddrzewo nowego seta *)
(* k - przedzial, ktory reprezentowany jest przez korzen nowego seta *)
(* r - prawe poddrzewo nowego seta *)
let make l k r =
  Node (l, k, r, max (height l) (height r) + 1,
    sum (sum (size l) (size r)) (interval k))


(* Funkcja balansujaca set o poddrzewach l i r
oraz przedziale k reprezentowanym przez korzen*)
let bal l k r =
  let hl = height l in
  let hr = height r in
  if hl > hr + 2 then
    match l with
    | Node (ll, lk, lr, _, _) ->
      if height ll >= height lr then make ll lk (make lr k r)
      else
        (match lr with
        | Node (lrl, lrk, lrr, _, _) ->
          make (make ll lk lrl) lrk (make lrr k r)
        | Empty -> assert false)
    | Empty -> assert false
  else if hr > hl + 2 then
    match r with
    | Node (rl, rk, rr, _, _) ->
      if height rr >= height rl then make (make l k rl) rk rr
      else
        (match rl with
        | Node (rll, rlk, rlr, _, _) ->
          make (make l k rll) rlk (make rlr rk rr)
        | Empty -> assert false)
    | Empty -> assert false
  else make l k r


(* Funkcja zwracajaca set bedacy polaczeniem innego seta i przedzialu x *)
(* Zwrocony set jest zrownowazony *)
let rec add_one x = function
  | Node (l, k, r, h, s) ->
  	let (a, b) = k in
  	let (a1, b1) = x in
    if b1 < a then
      let nl = add_one x l in
      bal nl k r
    else
      let nr = add_one x r in
      bal l k nr
  | Empty -> Node (Empty, x, Empty, 1, interval x)


(* Funkcja usuwajaca z seta minimalny element *)
(* Zwrocony set jest zrownowazony *)
let rec remove_min_elt = function
  | Node (Empty, _, r, _, _) -> r
  | Node (l, k, r, _, _) -> bal (remove_min_elt l) k r
  | Empty -> assert false


(* Funkcja laczaca set l i r z przedzialem v *)
(* Zwrocony set jest zrownowazony *)
(* l, v i r sa rozlaczne *)
(* Wszystkie przedzialy w l zawieraja mniejsze liczby niz przedzialy w r *)
let rec join l v r =
  match (l, r) with
  | (Empty, _) -> add_one v r
  | (_, Empty) -> add_one v l
  | (Node (ll, lv, lr, lh, _), Node (rl, rv, rr, rh, _)) ->
    if lh > rh + 2 then bal ll lv (join lr v r) else
    if rh > lh + 2 then bal (join l v rl) rv rr else
    make l v r


(* Funkcja laczaca sety t1 i t2 w jeden *)
(* Zwrocony set jest zrownowazony *)
(* Wszystkie przedzialy w t1 zawieraja mniejsze liczby niz przedzialy w t2 *)
let merge t1 t2 =
  match t1, t2 with
  | Empty, _ -> t2
  | _, Empty -> t1
  | _ ->
    let k = min_elt t2 in
    join t1 k (remove_min_elt t2)


(* Funkcja ta dzieli set s na 2 mniejsze *)
(* Zwraca ona set skladajacy sie z przedzialow o wartosciach mniejszych niz
liczba calkowita x, wartosc bool mowiaca czy x znajduje sie w secie, oraz
set skladajacy sie z przedzialow o wartosciach wiekszych niz liczba
calkowita x *)
(* Zwrocone sety sa zrownowazone *)
let split x s =
  let rec loop x = function
    | Empty -> (Empty, false, Empty)
    | Node (l, v, r, _, _) ->
    	let (a, b) = v in
      if x > a && x < b then (add_one (a, x - 1) l, true, add_one (x + 1, b) r)
    	else if x = a && x = b then (l, true, r)
    	else if x = a then (l, true, add_one (x + 1, b) r)
    	else if x = b then (add_one (a, x - 1) l, true, r)
      else if x < a then
        let (ll, pres, rl) = loop x l in (ll, pres, join rl v r)
      else
        let (lr, pres, rr) = loop x r in (join l v lr, pres, rr)
  in
  let setl, pres, setr = loop x s in (setl, pres, setr)


(* Funkcja zwracajaca true, jezeli liczba calkowita x znajduje sie
w secie s i false w przeciwnnym przypadku *)
let mem x s =
  let rec loop = function
    | Node (l, k, r, _, _) ->
      let (a, b) = k in
      (x >= a && x <= b) || loop (if x < a then l else r)
    | Empty -> false
  in loop s


(* Funkcja zwracajaca liste posortowanych rosnaco przedzialow w secie s *)
let elements s = 
  let rec loop acc = function
    | Empty -> acc
    | Node(l, k, r, _, _) -> loop (k :: loop acc r) l
  in loop [] s


(* Funkja nakladajaca funkcje f na kolejne przedzialy
w s (posortowane rosnac) *)
let iter (f : int * int -> unit) s =
  let rec loop = function
    | Empty -> ()
    | Node (l, k, r, _, _) -> loop l; f k; loop r
  in loop s


(* Funkja przyjmujaca funkcje f, set s oraz akumulator
wyniku acc i zwracajaca:
[(f xN ... (f x2 (f x1 acc))...)] *)
let fold f s acc =
  let rec loop acc = function
    | Empty -> acc
    | Node (l, k, r, _, _) ->
      loop (f k (loop acc l)) r
  in loop acc s


(* Funkcja zwracajaca ilosc elementow mniejszych od x
i znajdujacych sie na secie s *)
let rec below x s =
  match s with
  | Empty -> 0
  | Node (l, k, r, _, _) ->
    let (a, b) = k in
    if x >= a && x <= b then sum (interval (a, x)) (size l)
    else if x < a then below x l
    else sum (sum (size l) (interval k)) (below x r)


(* Funkcja usuwajaca przedzial [a, b] z s *)
(* Funkcja ta wywoluje 2 razy split w celu otrzymania
2 rozlacznych setow bez
przedzialu [a, b], a nastepnie je laczy *)
let remove (a, b) s =
  let (ls, _, _) = split a s in
  let (_, _, rs) = split b s in
  merge ls rs


(* Funkcja ta zwraca lewy koniec przedzialu, z ktorym zlaczylaby sie
liczba a gdyby zostala dodana do seta s *)
let rec lower s a =
  match s with
  | Empty -> a
  | Node (l, k, r, _, _) ->
    let (a1, b1) = k in
    if a >= a1 && a <= b1 then a1
    else if a > b1 then
      if a = b1 + 1 then a1
      else lower r a
    else lower l a


(* Funkcja ta zwraca prawy koniec przedzialu, z ktorym zlaczylaby sie
liczba a gdyby zostala dodana do seta s *)
let rec higher s a =
  match s with
  | Empty -> a
  | Node (l, k, r, _, _) ->
    let (a1, b1) = k in
    if a >= a1 && a <= b1 then b1
    else if a < a1 then
      if a <> a1 - 1 then higher l a
      else b1
    else higher r a


(* Funkcja dodajaca przedzial [a, b] do seta s *)
(* Funkcja ta najpierw ustala, do jakiego przedzialu rozszerzylby sie przedzial
[a, b], gdyby zostal dolaczony do s ([a1, b1]).
Potem uruchamia 2 splity, aby dostac 2 rozlaczne sety bez
[a1, b1], a nastepnie laczy ten przedzial z 2 powstalymi setami *)
let add (a, b) s =
  let a1 = lower s a in
  let b1 = higher s b in
  let (l, _, _) = split a1 s in
  let (_, _, r) = split b1 s in
  join l (a1, b1) r


(* TESTY *)
(*
let a = add (0, 5) empty;;
let a = add (-3, 5) a;;
let a = add (-100, -100) a;;
let a = add (6, 7) a;;
assert (elements a = [(-100, -100); (-3, 7)]);;
assert (below 8 a = 12);;
let b = add (6, 6) a;;
let b = remove (18, 19) b;;
let b = add (8, 8) b;;
let b = add (10, 10) b;;
assert (elements b = [(-100, -100); (-3, 8); (10, 10)]);;
assert (below 10 b = 14);;
let c = remove (2, 10) a;;
assert(elements c = [(-100, -100); (-3, 1)]);;
assert(below min_int c = 0);;
let e = add (-3, -1) empty;;
let f = add (1, 3) empty;;
let d = join e (0, 0) f;;
assert (elements d = [(-3, -1); (0, 0); (1, 3)]);;
assert (below 1000 d = 7);;
let g (a, b) acc = acc + a + b;;
assert (fold g a 0 = -196);;
assert (fold g b 0 = -175);;
assert (fold g c 0 = -202);;
assert (fold g d 0 = -0);;
assert (fold g e 0 = -4);;
assert (fold g f 0 = 4);;
let a = empty
let a = add (-20, 5) a
let a = add (6, 18) a
let a = add (4, 10) a
let a = add (14, 16) a
let a = remove (-18, 14) a
let a = remove (5, 17) a;;
assert (mem 14 a = false);;
let a = add (-4, 9) a;;
assert (mem 16 a = false);;
assert (mem (-14) a = false);;
assert (mem 10 a = false);;
let a = remove (-9, 10) a;;
let a = add (-6, 7) a;;
let a = add (-2, 7) a;;
let a = add (-12, 17) a;;
let a = add (-13, 8) a;;
let a = add (-13, -2) a;;
assert (mem 11 a = true);;
assert (elements a = [(-20, -19); (-13, 18)]);;
let (l, ex, r) = split 1 a;;
assert (ex = true);;
assert (mem 1 l = false);;
assert (mem 1 r = false);;
*)