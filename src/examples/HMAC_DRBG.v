Set Implicit Arguments.

Require Import FCF.
Require Import PRF.
Require Import Encryption.
(* Require Import Vector. *)

Opaque evalDist.
Opaque getSupport.

Local Open Scope nat_scope.
Local Open Scope type_scope.
(* Local Open Scope list_scope. *)

(* NIST standard:

http://csrc.nist.gov/publications/nistpubs/800-90A/SP800-90A.pdf

Functional HMAC-DRBG spec:

https://bitbucket.org/naphatkrit/rng
https://paper.dropbox.com/doc/RNG-Verification-Y4H1l2kXcHBfOwTczi8b9 *)

(* Pseudocode:

- Internal state: 
--> may need to pass around monadically?

  Change:
Value : Bvector outlen (secret)
Key : Bvector outlen (secret)
Counter : nat

  Don't change:
security_strength : nat
prediction_resistance_flag : bool

- Top-level input: 
HMAC : ...

- Top-level output: 
? : ...

Definition blist := list bool.
Definition outvec := outvec.

TODO: is there a difference between "do with adin = []" and "do with NO adin"?
TODO: all of the blists have a maximum length
TODO: which functions are called internally only? which externally?
TODO: just the important part of the Generate_function (no loop)

- PRG functions:
Update : (provided_data : blist) (key : outvec) (value : outvec) -> 
         (key : outvec) (value : outvec) <-- state instead?

Instantiate : (entropy_input : blist) (nonce : blist) (personalization_string : blist)
              (security_strength : nat) ->
              (initial_working_state : state)

Reseed_function : (working_state : state) (entropy_input : blist) (additional_input : blist)
                  -> (new_working_state : state)

Generate_function : (working_state : state) (requested_number_of_bits : nat) 
                    (additional_input : blist) ->
                    option ((returned_bits : outvec) * (new_working_state : state))

- API functions: (TODO)

Reseed : (Section 9.2, p30)

  -> option 
  ^^ difficulty: consuming function gets the status but not the state; DRBG retains state
     there are inputs that the consuming function provides but others that the the DRBG does

Generate : (Section 9.3, p32) *)

Section HMAC_DRBG_spec.

Definition blist := list bool.

(* HMAC defs *)
Variable keylen : nat.
Variable key : Bvector keylen.
Variable outlen : nat.
(* TODO check sizes + constraints on sizes *)
(* TODO other inputs like the hash function *)
Variable HMAC : Bvector keylen -> blist -> Bvector outlen.
Definition HMAC_k := HMAC key.
Definition HMAC_kl m := Vector.to_list (HMAC_k m).
(* Definition HMAC_kl' (m : Bvector n := HMAC_k (Vector.to_list m). *)
Variable V : Bvector outlen. 

(* Simplest version: running HMAC once will be indistinguishable from random *)
(* TODO or, given that HMAC is a PRF, use the PRF proof? or just use a PRF for now 
(using PRF advantage etc.) *)
(* TODO look at Adam's HMAC proof *)
Definition once : Bvector outlen :=
  HMAC_k (Vector.to_list V).



(* remove last n elements *)
Definition once_truncate (n : nat) (pf : n < outlen) : Bvector (outlen - n) :=
  Vector.trunc n pf (HMAC_k (Vector.to_list V)).

(* Twice *)
Definition twice : Bvector (outlen + outlen) :=
  let temp := [] in
  let v' := HMAC_k (Vector.to_list V) in
  let temp' := Vector.append temp v' in
  let v'' := HMAC_k (Vector.to_list v') in
  Vector.append temp' v''.

(* Slightly more complicated:
Core 'Generate' process (p48)
leaving out: reseeding, additional input, updating the state (key and V), reseed counter, 
  requested number of bits, HMAC as a parameter? HMAC's # bits?

hardcode: HMAC-256, outputs 256 bits, 256 bits requested (harder: 1024 bits req'd -> 4 loops)
DRBG : HMAC -> DRBG
Generate : state -> state

temp = Null

While (len(temp) < requested_number_of_bits) do:
  V = HMAC(Key, V)
  temp = temp || V

return leftmost requested_number_of_bits of temp *)

(* LIST VERSION *)
(* Applies f n times to the input *)
Fixpoint iterateN {A : Type} (f : A -> A) (a : A) (n : nat) : A :=
  match n with
  | O => a
  | S n' => iterateN f (f a) n'
  end.

(* Generates one more HMAC-output-length list of pseudorandom bits *)
Definition loop (tup : blist * blist) : blist * blist :=
  let (v, temp) := tup in
  let v' := HMAC_kl v in
  let temp' := temp ++ v' in
  (v', temp').

(* Generate a list of (n * HMAC-output-length) pseudorandom bits  *)
Definition Generate n :=
  let V_init := Vector.to_list V in
  let temp_init := nil in
  iterateN loop (V_init, temp_init) n.

(* VECTOR VERSION *)
(* Dependent type iteration?? pass length of vector around *)
(* Applies f n times to the input *)
(* Problem: f takes a nat which can't be named, but needs to be named
Problem: the output size might be either inlen or (inlen + outlen) 
Problem: do we need to return the output size? *)

Inductive Either (A : Type) : Type := 
  | Left : A -> Either A
  | Right : A -> Either A.

(* TODO: iterateN' does not check *)
Fixpoint iterateN' {A : Type} (inlen : nat) f
         (* (f : nat -> Bvector nat -> Bvector (nat + outlen)) *)
         (a : Bvector inlen) (n : nat) := Either Bvec
  (* : Bvector inlen or Bvector (inlen + outlen) := *)
  match n with
  | O => a
  | S n' =>
    let inlen' := inlen + outlen in a
    (* iterateN' bool inlen' (f inlen') (f inlen' a) n' *)
  end.

(* Generates one more HMAC-output-length list of pseudorandom bits *)
(* Question: should temp be a list or a Bvector whose size is passed around? *)
Definition loop' (n : nat) (tup : Bvector outlen * Bvector n) :
  Bvector outlen * Bvector (n + outlen) :=
  let (v, temp) := tup in
  let v' := HMAC_k (Vector.to_list v) in
  let temp' := Vector.append temp v' in
  (v', temp').

(* Generate a list of (n * HMAC-output-length) pseudorandom bits  *)
Definition Generate' (n : nat) : Bvector (n * outlen) :=
  (* let V_init := Vector.to_list V in *)
  let temp_init := nil in
  iterateN' loop' (V, temp_init) n.

End HMAC_DRBG_spec.
