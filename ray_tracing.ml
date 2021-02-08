Random.self_init ();
print_endline "Hello World";;

type vect = {x : float; y : float; z : float}
let cons_v a b c = {x=a; y=b; z=c}
let ( +~ ) u v = cons_v (u.x +. v.x) (u.y +. v.y) (u.z +. v.z)
let ( *~ ) l u = cons_v (l *. u.x) (l *. u.y) (l *. u.z)
let ( -~ ) u v = u +~ (-1.) *~ v
let inner u v = cons_v (u.x *. v.x) (u.y *. v.y) (u.z *. v.z)
let dot u v = (u.x *. v.x) +. (u.y *. v.y) +. (u.z *. v.z)
let norm u = dot u u |> sqrt
let normalize u = (1. /. (norm u)) *~ u
let cross u v = cons_v (u.y*.v.z-.u.z*.v.y) (u.z*.v.x-.u.x*.v.z) (u.x*.v.y-.u.y*.v.x)

let list_ij l c = List.init (l*c) (fun k -> (k/c, k-k/c*c));;

 (* Convention : P(t) = a + t*b;  ||b|| = 1 *)
type ray = {a : vect; b : vect}
type geometry = Sphere of vect * float
type material = Lambertian of vect | Metal of vect | Glass of float
type hittable = Hittable of geometry * material | HittableList of hittable list
type hitRecord = {mat : material; p : vect; n : vect; t : float}
type camera = {w : int; h : int; p: vect; vp_c : vect; vp_v: vect; vp_h: vect};;

let mycamera () =
  let ratio = 16./.9. in
  let width = 1440 in
  let pos = cons_v (0.5) (0.5) 2. in
  let dir = cons_v (1.) 1. (-.0.1) in
  let alpha = 0.4 in

  let z = (-1.)*~(normalize dir) in
  let x = normalize (cross (cons_v 0. 0. 1.) z) in
  let y = cross z x in
  {w=width; h=int_of_float (1./.ratio*.(float width)); p=pos; vp_c=pos-~z; vp_v=(tan alpha /. ratio)*~y; vp_h=(tan alpha)*~x};;

let mat_floor = Metal (cons_v 0.5 0.5 0.5)
let s1 = Hittable ((Sphere ((cons_v 15. 15. 2.), 2.)), (Metal (cons_v 0.5 0.5 0.5)))
let s2 = Hittable ((Sphere ((cons_v 15. 10. 2.), 2.)), (Glass 1.33))
let s3 = Hittable ((Sphere ((cons_v 15. 5. 2.), 2.)), (Lambertian (cons_v 1. 0. 0.)))
let random_color () = cons_v (Random.float 1.) (Random.float 1.) (Random.float 1.)
let random_material () =
  let i = Random.int 3 in
  if i = 0 then Metal (random_color ()) else
  if i = 1 then Lambertian (random_color ()) else
    Glass 1.33
let random_spheres =
  list_ij 20 20
  |> List.map (fun (i, j) -> (Hittable ((Sphere ((cons_v  (Random.float 1. +. float (2*i)) (Random.float 1. +. float (2*j)) (0.4) ), 0.4)), (random_material ())  )))
let world = HittableList (
    s1::s2::s3::(Hittable ((Sphere ((cons_v  0. 0. (-10000.), 10000.))), mat_floor)) :: random_spheres
  );;

let rec mininlist f = function
  | [] -> None
  | a::t ->
    match mininlist f t with
    | None -> Some a
    | Some m -> if f a m then Some a else Some m

let rec hit ray h = match h with
  | Hittable ((Sphere (sp, sr)), mat) ->
    let oc = ray.a -~ sp in
    let a, b, c = dot ray.b ray.b, 2. *. dot oc ray.b, dot oc oc -. sr *. sr in
    let d = b*.b -. 4.*.a*.c in
    if d < 0. then None else
      let t1 = (-.b -. (sqrt d)) /. (2.*.a) in
      let t2 = (-.b +. (sqrt d)) /. (2.*.a) in

      if t1 > 0.0001 then
        let p = ray.a +~ t1 *~ ray.b in
        let n = normalize (p -~ sp) in
        Some {mat; p; n; t=t1}
      else if t2 > 0.0001 then
        let p = ray.a +~ t2 *~ ray.b in
        let n = normalize (p -~ sp) in
        Some {mat; p; n; t=t2}
      else None

  | HittableList l ->
    let hrl = List.filter_map (hit ray) l in
    mininlist (fun hr1 hr2 -> hr1.t <= hr2.t) hrl

;;
let rec random_point_in_sphere rad pos =
  let v = cons_v (Random.float 1.) (Random.float 1.) (Random.float 1.) in
  let w = 2. *. rad *~ (v -~ (cons_v 0.5 0.5 0.5)) in
  if norm w < rad then pos +~ w else random_point_in_sphere rad pos

;;
let rec color_of_ray depth ray =
  if depth <= 0 then cons_v 0. 0. 0. else
    match hit ray world with
  (* | Some hr -> let n = 0.5 *~ hr.n +~ (cons_v 0.5 0.5 0.5) in n *)
    | Some hr ->
      let reflect uv nor = uv -~ 2. *. (dot uv nor) *~ nor in
      let refract uv nor ratio =
        let cos_theta = -. dot uv nor in
        let r_out_per = ratio *~ (uv +~ cos_theta *~ nor) in
        let r_out_par = (-. (sqrt (1. -. (dot r_out_per r_out_per)))) *~ nor in
        r_out_per +~ r_out_par in
      let schlick cosine ratio =
        let r0 = ((1.-.ratio)/.(1.+.ratio))**2. in
        r0 +. (1.-.r0)*.(1.-.cosine)**5. in
      begin
        match hr.mat with
        | Lambertian c ->
          let s = random_point_in_sphere 1. (hr.p +~ hr.n) in
          inner c  (color_of_ray (depth - 1) {a=hr.p; b=normalize (s -~ hr.p)})
        | Metal c ->
          inner c (color_of_ray (depth - 1) {a=hr.p; b=normalize (reflect ray.b hr.n)})
        | Glass n ->
          let (ratio, nor) = if dot ray.b hr.n <= 0. then 1./.n, hr.n else n, (-.1.) *~ hr.n in
          let r =
            let cos_theta = -. dot ray.b nor in
            let sin_theta = sqrt (1. -. cos_theta*.cos_theta) in
            if ratio *. sin_theta >= 1. || schlick cos_theta ratio > Random.float 1. then
              reflect ray.b nor
            else refract ray.b nor ratio
          in
          color_of_ray (depth - 1) {a=hr.p; b=normalize r}
      end
    | None -> let t = 0.5 *. ray.b.z +. 0.5 in (1.0 -. t) *~ (cons_v 1.0 1.0 1.0) +~ t *~ (cons_v 0.2 0.2 1.0)

;;
let compute_rays rpp ca =
  let corner_bl = ca.vp_c -~ ca.vp_h -~ ca.vp_v in
  let flpixels_to_ray l c =
    let v = corner_bl +~ c /. float_of_int ca.w *. 2. *~ ca.vp_h +~ (float ca.h -. l) /. float_of_int ca.h *. 2. *~ ca.vp_v in
    {a = ca.p; b = normalize (v-~ca.p)}
  in
  Parmap.L (list_ij ca.h ca.w)
  |> Parmap.parmap ~ncores:4 ~chunksize:100 ~keeporder:true
    (fun (l, c) ->
       List.init rpp (fun _ -> flpixels_to_ray ((float l) +. Random.float 1.)  ((float c) +. Random.float 1.))
       |> List.map (color_of_ray 10)
       |> List.fold_left ( +~ ) (cons_v 0. 0. 0.)
       |> (fun v -> (1./.(float rpp)) *~ v)
       |> (fun v -> cons_v (sqrt v.x) (sqrt v.y) (sqrt v.z))
       |> (fun col -> Format.sprintf "%i %i %i" (int_of_float (col.x *. 255.)) (int_of_float (col.y *. 255.)) (int_of_float (col.z *. 255.)))
    )
  |> String.concat "\n"
  |> Format.sprintf "P3\n%i %i\n255\n%s\n" ca.w ca.h;;
;;

let channel = open_out "temp.ppm" in
mycamera ()
|> compute_rays 200
|> output_string channel;
close_out channel;
let result = Sys.command "convert temp.ppm image.png && eog -w image.png &" in
  Format.printf "Result is : %i\n" result
;;
