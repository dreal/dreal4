;; https://github.com/dreal/dreal4/issues/228
;; expected: delta-sat

(declare-fun sides () Int)
(assert (or (= sides 3) (= sides 4)))
(declare-fun vertices () Int)
(assert (or (= vertices 3) (= vertices 4)))

;type: 0=triangle, 1=quadrilateral
(declare-fun type () Int)
(assert (or (= type 0) (= type 1)))

(declare-fun length1 () Real)
(declare-fun length2 () Real)
(declare-fun length3 () Real)
(declare-fun length4 () Real)
(declare-fun angle1 () Real)
(declare-fun angle2 () Real)
(declare-fun angle3 () Real)
(declare-fun angle4 () Real)

(declare-fun pi () Real)
(assert (= pi 3.14159265358979323846264338327950288419716939937510))

;subtype:  0=regular_triangle
;        , 1=right_triangle
;        , 2=rectangle
;        , 3=square
;        , 4=irregular
(declare-fun subtype () Int)
(assert (and (>= subtype 0) (<= subtype 4)))

(declare-fun convex () Bool)
(declare-fun equilateral () Bool)
(declare-fun perimeter () Real)

;coordinates

(declare-fun vert3x () Real)
(declare-fun vert3y () Real)
(declare-fun vert4x () Real)
(declare-fun vert4y () Real)

;surface

(declare-fun surface () Real)


(declare-fun epsilon () Real)
(assert (= epsilon 0.1))

;THEORY

;[Definition of triangle] remove explain3
(assert (= (= type 0) (= sides 3)))

;[Definition of rectangle]
(assert (= (= type 1) (= sides 4)))

;[There are as many vertices as there are sides]
(assert (and (= (= vertices 3) (= sides 3))
      (= (= vertices 4) (= sides 4))))

;[All triangles are convex]
(assert (=> (= sides 3) (= convex true)))

;[Definition of Convex: All angles are below 180°]
(assert (= (= convex true) (and (< angle1 pi) (< angle2 pi) (< angle3 pi) (< angle4 pi))))

;[Definition of Equilateral: All sides have the same length]
(assert (= equilateral (and (or (= length2 length1) (= length2 0)) (or (= length3 length1) (= length3 0)) (or (= length4 length1) (= length4 0)))))

;[A triangle is regular, right, or irregular]
(assert (=> (= sides 3) (or (= subtype 0) (= subtype 1) (= subtype 4))))

;[A regular triangle is an equilateral triangle]
(assert (= (= subtype 0) (and (= sides 3) (= equilateral true))))

;[A regular triangle is a triangle where all angles are 60°]
(declare-fun allangle60 () Bool)
(assert (= (= subtype 0) (and (= sides 3) (= allangle60 true))))
;all angles are 60°
(assert (= (= allangle60 true) (and (or (= angle1 (/ pi 3)) (= angle1 0)) (or (= angle2 (/ pi 3)) (= angle2 0)) (or (= angle3 (/ pi 3)) (= angle3 0)) (or (= angle4 (/ pi 3)) (= angle4 0)))))

;[A right triangle is a triangle with a 90° angle]
(declare-fun oneangle90 () Bool)
(assert (= (= subtype 1) (and (= sides 3) (= oneangle90 true))))
;one angle is 90°
(assert (= (= oneangle90 true) (or (= angle1 (/ pi 2)) (= angle2 (/ pi 2)) (= angle3 (/ pi 2)) (= angle4 (/ pi 2)))))

;[All angles are 90° in squares and rectangles]
(declare-fun allangle90 () Bool)
(assert (= (or (= subtype 2) (= subtype 3)) (and (= sides 4) (= allangle90 true))))
;All angles are 90°
(assert (= (= allangle90 true) (and (or (= angle1 (/ pi 2)) (= angle1 0)) (or (= angle2 (/ pi 2)) (= angle2 0)) (or (= angle3 (/ pi 2)) (= angle3 0)) (or (= angle4 (/ pi 2)) (= angle4 0)))))

;[In a rectangle, opposite side have the same length, and adjacent sides have different lengths]
(assert (=> (= subtype 2) (and (= length1 length3) (= length2 length4) (not (= length1 length2)))))

;[A square is an equilateral quadrilateral]
(assert (= (= subtype 3) (and (= sides 4) (= equilateral true))))

;[In a triangle, no side is longer than the sum of the 2 other sides]
(assert (=> (= type 0) (and (< length1 (+ length2 length3))
                            (< length2 (+ length3 length1))
                            (< length3 (+ length1 length2)))))


;General constraints

;[The perimeter is the sum of the lengths of the sides]
(assert (= perimeter (+ length1 length2 length3 length4)))

;[The sum of the angles is 180° for a triangle, and 360° for a quadrilateral]
(assert (= (+ angle1 angle2 angle3 angle4) (* (- sides 2) pi)))

;[Lengths are positive numbers]
(assert (<= 0 length1))
(assert (<= 0 length2))
(assert (<= 0 length3))
(assert (<= 0 length4))

;[Angles are positive numbers]
(assert (<= 0 angle1))
(assert (<= 0 angle2))
(assert (<= 0 angle3))
(assert (<= 0 angle4))

;[Angles cannot be 180°]
(assert (not (= pi angle1)))
(assert (not (= pi angle2)))
(assert (not (= pi angle3)))
(assert (not (= pi angle4)))

;[A polygon with N vertices has N angles]
(assert (= (= angle1 0) (< vertices 1)))
(assert (= (= angle2 0) (< vertices 2)))
(assert (= (= angle3 0) (< vertices 3)))
(assert (= (= angle4 0) (< vertices 4)))

;[A polygon with N sides has N lengths]
(assert (= (= length1 0) (< sides 1)))
(assert (= (= length2 0) (< sides 2)))
(assert (= (= length3 0) (< sides 3)))
(assert (= (= length4 0) (< sides 4)))

;coordinates

(assert (= vert3x (- length1 (* (cos angle2) length2))))
(assert (= vert3y (* (sin angle2) length2)))

(assert (= vert4x (* (cos angle1) length4)))
(assert (= vert4y (* (sin angle1) length4)))

(assert (= vert4x (- vert3x (* (cos (+ angle3 (- angle2 pi))) length3))))
(assert (= vert4y (+ vert3y (* (sin (+ angle3 (- angle2 pi))) length3))))

;surface

(assert (> surface 0))
(assert (=> convex (= surface (/ (+ (* length1 (* length4 (sin angle1))) (* length2 (* length3 (sin angle3)))) 2))))

(assert (<= length1 2000000))
(assert (<= length2 2000000))
(assert (<= length3 2000000))
(assert (<= length4 2000000))
(assert (<= angle1 2000000))
(assert (<= angle2 2000000))
(assert (<= angle3 2000000))
(assert (<= angle4 2000000))
(assert (<= perimeter 2000000))
(assert (>= perimeter 0))
(assert (<= surface 2000000))
(assert (<= vert3x 2000000))
(assert (<= vert3y 2000000))
(assert (<= vert4x 2000000))
(assert (<= vert4y 2000000))
(assert (>= vert3x (- 2000000)))
(assert (>= vert3y (- 2000000)))
(assert (>= vert4x (- 2000000)))
(assert (>= vert4y (- 2000000)))

(assert (= angle3 (/ pi 3)))
(assert (= length2 10))
(assert (= length3 7))
(assert (= angle2 (* 100 (/ pi 180))))

(check-sat)
(exit)
