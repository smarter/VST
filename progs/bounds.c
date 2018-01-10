#include <stddef.h>
#include <stdint.h>

typedef int od_coeff;

#define INLINE

#define AVG_BIAS (0)

static INLINE od_coeff od_add(od_coeff p0, od_coeff p1) {
  return p0 + p1;
}

static INLINE od_coeff od_sub(od_coeff p0, od_coeff p1) {
  return p0 - p1;
}

static INLINE od_coeff od_add_avg(od_coeff p0, od_coeff p1) {
  return (od_add(p0, p1) + AVG_BIAS) >> 1;
}

static INLINE od_coeff od_sub_avg(od_coeff p0, od_coeff p1) {
  return (od_sub(p0, p1) + AVG_BIAS) >> 1;
}

/* Fixed point multiply. */
static INLINE od_coeff od_mul(od_coeff n, int c, int q) {
  return (n*c + ((1 << q) >> 1)) >> q;
}

/* Two multiply rotation primative (used when rotating by Pi/4). */
static INLINE void od_rot2(od_coeff *p0, od_coeff *p1, od_coeff t, int c0,
 int q0, int c1, int q1) {
  *p1 = od_mul(*p0, c0, q0);
  *p0 = od_mul(t, c1, q1);
}

#define NONE (0)
#define AVG (!NONE)
#define SHIFT (!NONE)

#define ADD (0)
#define SUB (1)

/* Rotate by Pi/4 and add. */
static INLINE void od_rotate_pi4_kernel(od_coeff *p0, od_coeff *p1, int c0,
 int q0, int c1, int q1, int type, int avg) {
  od_coeff t;
  t = type == ADD ?
   avg ? od_add_avg(*p1, *p0) : od_add(*p1, *p0) :
   avg ? od_sub_avg(*p1, *p0) : od_sub(*p1, *p0);
  od_rot2(p0, p1, t, c0, q0, c1, q1);
  *p1 = type == ADD ? od_sub(*p1, *p0) : od_add(*p1, *p0);
}

#define od_rotate_pi4_sub_avg(p0, p1, c0, q0, c1, q1) \
 od_rotate_pi4_kernel(p0, p1, c0, q0, c1, q1, SUB, AVG)

/**
 * 2-point orthonormal Type-II fDCT
 */
/*static INLINE*/ void od_fdct_2(od_coeff *p0, od_coeff *p1) {
  /* 11585/8192 = Sin[Pi/4] + Cos[Pi/4]  = 1.4142135623730951 */
  /* 11585/8192 = 2*Cos[Pi/4]            = 1.4142135623730951 */
  od_rotate_pi4_sub_avg(p1, p0, 11585, 13, 11585, 13);
}

int main() {
  return 0;
}
