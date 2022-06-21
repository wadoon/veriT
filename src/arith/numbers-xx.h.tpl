/* -*- mode: C -*-
   --------------------------------------------------------------
   Types and functions to deal with numbers.

   There are two versions: HW (hardware) and MP (multi-precision).

   Common definitions are in *-xx-*.tpl files (tpl for template),
   where the strings xx and XX represent the version. These files
   are then processed by cpp with xx=hw, XX=HW and xx=mp, XX=MP
   to generate C code.

   Some specific definitions are found in sections of the template
   files guarded by conditional preprocessor directives, and others
   are coded directly in some C file.
   --------------------------------------------------------------
*/

#ifndef __NUMBERS_XX_H
#define __NUMBERS_XX_H

#define XX_VERSION

#include <stdbool.h>
#include <stdio.h>

/*
  --------------------------------------------------------------
  Overflow stuff
  --------------------------------------------------------------
*/

#ifdef HW_VERSION

/**
   \author Pascal Fontaine
   \brief records if any overflow has taken place */
extern bool LA_overflow;

#define RETURN_IF_OVERFLOW(A) \
	{ \
		if (LA_overflow) return A; \
	}

#ifdef DEBUG_EXCEPTION_OVERFLOW
#define THROW_OVERFLOW_WARNING my_warning("overflow\n");
#else
#define THROW_OVERFLOW_WARNING
#endif

/** \brief set global overflow subject to a condition */
#define OVERFLOW_CHECK(cond) \
	{ \
		if (cond) { \
			LA_overflow = 1; \
			THROW_OVERFLOW_WARNING; \
		} \
	}
#define OVERFLOW_CHECK_GOTO(cond) \
	{ \
		if (cond) { \
			LA_overflow = 1; \
			THROW_OVERFLOW_WARNING; \
			goto on_overflow; \
		} \
	}
#define OVERFLOW_CHECK_SET(cond, val) \
	{ \
		if (cond) { \
			LA_overflow = 1; \
			THROW_OVERFLOW_WARNING; \
			val = 1; \
		} \
	}
#else /* MP_VERSION */

#define RETURN_IF_OVERFLOW(A)

#endif

#include <gmp.h>

/*
  --------------------------------------------------------------
  Utils
  --------------------------------------------------------------
*/

#ifdef HW_VERSION

/** \brief Greatest common divisor */
unsigned gcd(const unsigned a, const unsigned b);

/**
   \brief Absolute value for signed integers.
   \param[in] __in a signed value
   \param[out] __out a signed lvalue */
#define SIGNED_ABS(__in, __out) \
	{ \
		signed __mask; \
		__mask = (__in) >> (sizeof(signed int) * CHAR_BIT - 1); \
		(__out) = (unsigned)(((__in) + __mask) ^ __mask); \
	}

#endif /* HW_VERSION */

/*
  --------------------------------------------------------------
  Signed
  --------------------------------------------------------------
*/

/**
   \author Pascal Fontaine
   \typedef TLAsigned_xx
   \brief signed number
   \remark C native signed long, but arbitrary size are available if needed
   \remark max signed long is 2^31-1 on 32 bits, 2^63-1 on 64 bits
   \remark min signed long is -2^31+1 on 32 bits, -2^63+1 on 64 bits
   \remark in principle, min unsigned long could be one less, but for
   simplicity in overflow detection, we will loose the LONG_MIN value
   \remark we use long long to detect overflow and compute gcd afterwards
   However, in this module, we will never let a stable value be larger
   than 32 bits */
#ifdef HW_VERSION
typedef signed int TLAsigned_xx;
#define LAsigned_xx_init(a)
#define LAsigned_xx_set(a, b) (a) = (b)
#define LAsigned_xx_clear(a)
#else
typedef mpz_t TLAsigned_xx;
#define LAsigned_xx_init mpz_init
#define LAsigned_xx_set mpz_set
#define LAsigned_xx_clear mpz_clear
#endif

/**
   \author Pascal Fontaine
   \brief executes the following operation a = a * b
   \param[in,out] a lvalue storing a TLAsigned_xx
   \param[in] b a TLAsigned_xx expression */
#ifdef HW_VERSION
#define LAsigned_xx_mult(a, b) \
	{ \
		signed long long tmp1; \
		tmp1 = (signed long long)a * (signed long long)b; \
		OVERFLOW_CHECK_SET(tmp1 > INT_MAX || tmp1 <= INT_MIN, tmp1); \
		a = (signed int)tmp1; \
	}
#else
#define LAsigned_xx_mult(a, b) mpz_mul(a, a, b);
#endif

/**
   \author David Deharbe
   \brief executes the following operation a = -(b * c)
   \param[in] a LAsigned
   \param[in] b LAsigned
   \param[out] c LAsigned */
#ifdef HW_VERSION
#define LAsigned_xx_mult_neg(a, b, c) \
	{ \
		signed long long tmp1; \
		tmp1 = (signed long long)b * (signed long long)c; \
		OVERFLOW_CHECK_SET(tmp1 > INT_MAX || tmp1 <= INT_MIN, tmp1) \
		a = -(signed int)tmp1; \
	}
#else
#define LAsigned_xx_mult_neg(a, b, c) \
	{ \
		mpz_mul(a, b, c); \
		mpz_neg(a, a); \
	}
#endif

/**
   \author Pascal Fontaine
   \brief executes the following operation a = -b
   \param[out] a LAsigned
   \param[in] b LAsigned */
#ifdef HW_VERSION
#define LAsigned_xx_neg(a, b) (a) = -(b)
#else
#define LAsigned_xx_neg(a, b) mpz_neg(a, b)
#endif

/**
   \author Pascal Fontaine
   \brief execute the following operation a = a * c - b * d
   \param[in,out] a LAsigned
   \param[in] b LAsigned
   \param[in] c LAsigned
   \param[in] d LAsigned */
#ifdef HW_VERSION
#define LAsigned_xx_com(a, b, c, d) \
	{ \
		signed long long tmp1, tmp2; \
		tmp1 = (signed long long)a * (signed long long)c; \
		tmp2 = (signed long long)b * (signed long long)d; \
		OVERFLOW_CHECK_SET(tmp1 > INT_MAX || tmp1 <= INT_MIN, tmp1); \
		OVERFLOW_CHECK_SET(tmp2 > INT_MAX || tmp2 <= INT_MIN, tmp2); \
		tmp1 -= tmp2; \
		OVERFLOW_CHECK_SET(tmp1 > INT_MAX || tmp1 <= INT_MIN, tmp1); \
		a = (signed int)tmp1; \
	}
#else
#define LAsigned_xx_com(a, b, c, d) \
	{ \
		mpz_mul(a, a, c); \
		mpz_submul(a, b, d); \
	}
#endif

/**
   \author Pascal Fontaine
   \brief sets a LAsigned value
   \param[out] a LAsigned
   \param[in] b a signed long int */
#ifdef HW_VERSION
#define LAsigned_xx_set_si(a, b) \
	{ \
		a = b; \
	}
#else
#define LAsigned_xx_set_si(a, b) mpz_set_si(a, b)
#endif

/**
   \author Pascal Fontaine
   \brief check if a signed value is 0
   \param[in] a LAsigned
   \return true iff a is zero */
#ifdef HW_VERSION
#define LAsigned_xx_is_zero(a) ((a) == 0)
#else
#define LAsigned_xx_is_zero(a) (mpz_sgn(a) == 0)
#endif

/**
   \author Pascal Fontaine
   \brief check if a signed value is < 0
   \param[in] a LAsigned
   \return true iff a is zero */
#ifdef HW_VERSION
#define LAsigned_xx_is_neg(a) ((a) < 0)
#else
#define LAsigned_xx_is_neg(a) (mpz_sgn(a) < 0)
#endif

/**
   \author Pascal Fontaine
   \brief checks if a and b have different sign
   \param[in] a pointer to a LAsigned
   \param[in] b pointer to a LAsigned
   \return true iff signs differ */
#ifdef HW_VERSION
#define LAsigned_xx_neq(a, b) (a != b)
#else
#define LAsigned_xx_neq(a, b) (mpz_cmp(a, b))
#endif

/**
   \author Pascal Fontaine
   \brief checks if a and b have different sign
   \param[in] a pointer to a LAsigned
   \param[in] b pointer to a LAsigned
   \return true iff signs differ */
#ifdef HW_VERSION
#define LAsigned_xx_sign_diff(a, b) \
	(((unsigned long)((a) ^ (b))) >> (sizeof(signed long) * CHAR_BIT - 1))
#else
#define LAsigned_xx_sign_diff(a, b) (mpz_sgn(a) != mpz_sgn(b))
#endif

/**
   \author Pascal Fontaine
   \brief prints a on stdout
   \param[in] a LAsigned */
#ifdef HW_VERSION
#define LAsigned_xx_print(a) printf("%d", a)
#else
#define LAsigned_xx_print(a) mpz_out_str(stdout, 10, a)
#endif

/**
   \author Pascal Fontaine
   \brief executes the following operation a = abs(b)
   \param[in,out] a lvalue storing a TLAsigned_xx
   \param[in] b a TLAsigned_xx expression */
#ifdef HW_VERSION
#define LAsigned_xx_abs(a, b) \
	{ \
		signed __mask; \
		__mask = (b) >> (sizeof(signed int) * CHAR_BIT - 1); \
		(a) = (((b) + __mask) ^ __mask); \
	}
#else
#define LAsigned_xx_abs(a, b) mpz_abs(a, b)
#endif

/**
   \author Pascal Fontaine
   \brief executes the following operation a = gcd(a, b)
   \param[in,out] a lvalue storing a TLAsigned_xx
   \param[in] b a TLAsigned_xx expression */
#ifdef HW_VERSION
#define LAsigned_xx_gcd(a, b) a = (signed)gcd((unsigned)(a), (unsigned)(b))
#else
#define LAsigned_xx_gcd(a, b) mpz_gcd(a, a, b)
#endif

/**
   \author Pascal Fontaine
   \brief tests if signed is different from one
   \param[in] a tested value */
#ifdef HW_VERSION
#define LAsigned_xx_notone(a) ((a) != 1)
#else
#define LAsigned_xx_notone(a) mpz_cmp_ui(a, 1UL)
#endif

/**
   \author Pascal Fontaine
   \brief tests if signed is strictly positive
   \param[in] a tested value */
#ifdef HW_VERSION
#define LAsigned_xx_pos(a) ((a) > 0)
#else
#define LAsigned_xx_pos(a) (mpz_cmp_ui(a, 0UL) > 0)
#endif /* HW_VERSION */

/**
   \author Pascal Fontaine
   \brief tests if one signed is strictly smaller than another signed
   \param[in] a first tested value
   \param[in] b second tested value */
#ifdef HW_VERSION
#define LAsigned_xx_smaller(a, b) ((a) < (b))
#else
#define LAsigned_xx_smaller(a, b) (mpz_cmp(a, b) < 0)
#endif /* HW_VERSION */

/**
   \author Pascal Fontaine
   \brief Divides signed a exactly by signed b, and assigns result to a
   \param[in, out] a dividend
   \param[in] b divisor
   \pre the remainder of the division of a by b is 0 */
#ifdef HW_VERSION
#define LAsigned_xx_divex(a, b) (a) /= (b)
#else
#define LAsigned_xx_divex(a, b) mpz_divexact(a, a, b)
#endif /* HW_VERSION */

/**
   \author Pascal Fontaine
   \brief Computes a key from a signed (e.g., for storing in a hash table)
   \param[in] a signed value */
#ifdef HW_VERSION
#define LAsigned_xx_key(a) ((unsigned)a)
#else
#define LAsigned_xx_key(a) ((unsigned)mpz_get_ui(a))
#endif /* HW_VERSION */

/*
  --------------------------------------------------------------
  Rationals
  --------------------------------------------------------------
*/

/**
   \author Pascal Fontaine
   \typedef TLArational_xx
   \brief rational number
   \remark pair of C native int
   \remark INT_MIN is counted as overflow in num */
#ifdef HW_VERSION
typedef struct TLArational_xx
{
	signed int num;
	unsigned int den;
} TLArational_xx[1];
#define LArational_xx_init(a)
#define LArational_xx_set(a, b) ((*a) = (*b))
#define LArational_xx_clear(a)
#define LArational_xx_set_si(a, b) \
	do { \
		a->num = b; \
		a->den = 1; \
	} while (0)
#else
typedef mpq_t TLArational_xx;
#define LArational_xx_init mpq_init
#define LArational_xx_set mpq_set
#define LArational_xx_clear mpq_clear
#define LArational_xx_set_si mpq_set_z
#endif

/**
   \author Pascal Fontaine
   \brief set a rational value to 1
   \param[out] rational a rational value */
void LArational_xx_set_one(TLArational_xx rational);

/**
   \author Rodrigo Castano
   \brief set a rational value to 0
   \param[out] rational a rational value */
void LArational_xx_set_zero(TLArational_xx rational);

/**
   \author Pascal Fontaine
   \brief check if a rational value is 0
   \param[in] rational a rational
   \return 1 if rational is zero */
bool LArational_xx_is_zero(TLArational_xx rational);

/**
   \author Pascal Fontaine
   \brief sets rational to be the number represented by str
   \param[out] rational a rational value (in canonical form)
   \param[in] str a string */
void LArational_xx_str(TLArational_xx rational, char* str);

/**
   \author Pascal Fontaine
   \brief sets rational to be the number represented by mpz
   \param[out] rational a rational value (in canonical form)
   \param[in] mpz a multiprecision integer */
void LArational_xx_mpz(TLArational_xx rational, mpz_t mpz);

/**
   \author Pascal Fontaine
   \brief sets rational to be the number represented by mpq
   \param[out] rational a rational value (in canonical form)
   \param[in] mpq a multiprecision rational */
void LArational_xx_mpq(TLArational_xx rational, mpq_t mpq);

/**
   \author Pascal Fontaine
   \brief normalize the value, i.e. divides num and den by their gcd
   \param[in,out] rational a rational value */
void LArational_xx_normalize(TLArational_xx rational);

/**
   \author Pascal Fontaine
   \brief changes sign of rational
   \param[in,out] rational a rational value */
void LArational_xx_neg(TLArational_xx rational);

/**
   \author Pascal Fontaine
   \brief check if a rational value is < 0
   \param[in] rational a rational
   \return 1 if rational is < 0 */
bool LArational_xx_is_neg(TLArational_xx rational);

/**
   \author David Deharbe
   \brief check if a rational value is integer
   \param[in] rational a rational
   \return 1 if rational is an integer */
bool LArational_xx_is_int(TLArational_xx rational);

/**
   \author Pascal Fontaine
   \brief adds two rationals and puts result in first argument
   \param[in,out] rational1 a first rational value
   \param[in] rational2 a second rational value
   \remark normalizes */
void LArational_xx_add(TLArational_xx rational1, TLArational_xx rational2);

/**
   \author Pascal Fontaine
   \brief multiplies two rationals and puts result in first argument
   \param[in,out] rational1 a first rational value
   \param[in] rational2 a second rational value
   \remark normalizes */
void LArational_xx_mult(
	TLArational_xx rational1, const TLArational_xx rational2);

/**
   \author Pascal Fontaine
   \brief multiply a rational by a signed and put result in first argument
   \param[in,out] rational1 a rational value
   \param[in] signed2 a signed value
   \remark normalizes */
void LArational_xx_mult_s(TLArational_xx rational1, TLAsigned_xx signed2);

/**
   \author Pascal Fontaine
   \brief divides two rationals and puts result in first argument
   \param[in,out] rational1 a rational value
   \param[in] rational2 a rational value
   \remark normalizes */
void LArational_xx_div(TLArational_xx rational1, TLArational_xx rational2);

/**
   \author Pascal Fontaine
   \brief multiplies a rational by a signed and puts result in first argument
   \param[in,out] rational1 a rational value
   \param[in] signed2 a signed value
   \remark normalizes */
void LArational_xx_mult_s(TLArational_xx rational1, TLAsigned_xx signed2);

/**
   \author Pascal Fontaine
   \brief divides a rational by a signed and puts result in first argument
   \param[in,out] rational1 a rational value
   \param[in] signed2 a signed value
   \remark normalizes */
void LArational_xx_div_s(TLArational_xx rational1, TLAsigned_xx signed2);

/**
   \author Pascal Fontaine
   \brief compares two rationals
   \param[in] rational1 a rational value a
   \param[in] rational2 a rational value b
   \return true iff a is equal to b */
bool LArational_xx_eq(TLArational_xx rational1, TLArational_xx rational2);

/**
   \author Pascal Fontaine
   \brief compares two rationals
   \param[in] rational1 a rational value a
   \param[in] rational2 a rational value b
   \return true iff a is smaller than or equal to b */
bool LArational_xx_leq(TLArational_xx rational1, TLArational_xx rational2);

/**
   \author Pascal Fontaine
   \brief compares two rationals
   \param[in] rational1 a rational value a
   \param[in] rational2 a rational value b
   \return true iff a is strictly smaller than b */
bool LArational_xx_less(TLArational_xx rational1, TLArational_xx rational2);

#ifdef HW_VERSION
/**
   \author Pascal Fontaine
   \brief gets the lcm of the denominator of *Prational and *Plcm
   \param[in,out] lcm a signed value
   \param[in] rational a rational value
   \remark stores the result in *Plcm */
#define LArational_xx_lcm(lcm, rational) LArational_xx_lcm_aux(&(lcm), rational)
void LArational_xx_lcm_aux(TLAsigned_xx* Plcm, TLArational_xx rational);
#else
/**
   \author Pascal Fontaine
   \brief gets the lcm of the denominator of *Prational and *Plcm
   \param[in,out] lcm a signed value
   \param[in] rational a rational value
   \remark stores the result in *Plcm */
void LArational_xx_lcm(TLAsigned_xx lcm, TLArational_xx rational);
#endif

#ifdef HW_VERSION
/**
   \author Pascal Fontaine
   \brief multiplies asigned by rational
   \param[in,out] asigned a lvalue containing signed value
   \param[in] rational a rational value
   \pre asigned is a multiple of rational's denominator.
   \remark stores the result in asigned
   \remark the result should be integer */
#define LArational_xx_mult_to_signed(asigned, rational) \
	LArational_xx_mult_to_signed_aux(&(asigned), rational)
void LArational_xx_mult_to_signed_aux(
	TLAsigned_xx* Pasigned, TLArational_xx rational);
#else
/**
   \author Pascal Fontaine
   \brief multiplies asigned by rational
   \param[in,out] asigned a signed value
   \param[in] rational a rational value
   \remark stores the result in asigned
   \remark the result should be integer */
void LArational_xx_mult_to_signed(
	TLAsigned_xx asigned, TLArational_xx rational);
#endif

/**
   \brief prints a rational
   \param[in,out] a rational
   \remark for debuging purposes */
#ifdef HW_VERSION
#define LArational_xx_print(a) printf("%d / %u", a->num, a->den)
#else
#define LArational_xx_print(a) mpq_out_str(stdout, 10, a)
#endif

/*
  --------------------------------------------------------------
  Delta numbers
  --------------------------------------------------------------
*/

/**
   \author Pascal Fontaine
   \typedef TLAdelta_xx
   \brief number with delta */
#ifdef HW_VERSION
typedef struct TLAdelta_xx
{
	struct TLArational_xx val;
	struct TLArational_xx delta;
} TLAdelta_xx;
#define LAdelta_xx_init(a)
#define LAdelta_xx_set(dst, src) (*dst) = (*src)
#define LAdelta_xx_clear(a)
#else
typedef struct TLAdelta_xx
{
	TLArational_xx val;
	TLArational_xx delta;
} TLAdelta_xx;
void LAdelta_xx_init(TLAdelta_xx*);
void LAdelta_xx_set(TLAdelta_xx* dst, TLAdelta_xx* src);
void LAdelta_xx_clear(TLAdelta_xx*);
#endif

#ifdef HW_VERSION
#define LAdelta_xx_set_rat(dst, src) (*dst).val = (**src)
#define LAdelta_xx_set_delta(dst, eps) \
	(*dst).delta.num = eps; \
	(*dst).delta.den = 1;
#define LAdelta_xx_get_rat(src, num, den) \
	{ \
		(num) = ((src).val.num); \
		(den) = (signed)((src).val.den); \
	}
#else
void LAdelta_xx_set_rat(TLAdelta_xx* dst, TLArational_xx* src);
void LAdelta_xx_set_delta(TLAdelta_xx* dst, int eps);
void LAdelta_xx_get_rat(
	TLAdelta_xx* src, TLAsigned_xx* Pnum, TLAsigned_xx* Pden);
#define LAdelta_xx_get_rat(src, num, den) \
	{ \
		(num) = (mpq_numref((src).val)); \
		(den) = (mpq_denref((src).val)); \
	}
#endif

/**
   \author Pascal Fontaine
   \brief sets delta value to 0
   \param[out] delta value */
void LAdelta_xx_set_zero(TLAdelta_xx* delta);

/**
   \author Pascal Fontaine
   \brief sets delta value to 1
   \param[out] delta value */
void LAdelta_xx_set_one(TLAdelta_xx* delta);

/**
   \author Pascal Fontaine
   \brief checks if delta is 0
   \param[in] delta value
   \return true iff zero */
bool LAdelta_xx_is_zero(TLAdelta_xx* delta);

/**
   \author David Deharbe
   \brief checks if delta is an integer
   \param[in] delta value
   \return true iff delta is integer-valued
   \pre value delta must be normalized
   \sa LAdelta_xx_normalize */
bool LAdelta_xx_is_int(TLAdelta_xx* delta);

/**
   \author Pascal Fontaine
   \brief sets value of delta according to int
   \param[out] delta
   \param[in] val its value */
void LAdelta_xx_int(TLAdelta_xx* delta, int val);

/**
   \author Pascal Fontaine
   \brief sets value of delta according to arguments
   \param[out] delta
   \param[in] num numerator for its value
   \param[in] den denominator for its value */
void LAdelta_xx_rat(TLAdelta_xx* delta, int num, unsigned den);

/**
   \author Pascal Fontaine
   \brief sets value of delta according to arguments
   \param[out] delta
   \param[in] num numerator for its value
   \param[in] den denominator for its value
   \param[in] eps coefficient of delta value */
void LAdelta_xx_rat_delta(TLAdelta_xx* delta, int num, unsigned den, int eps);

/**
   \author Pascal Fontaine
   \brief checks if two delta values are equal
   \param[in] delta1 value
   \param[in] delta2 value
   \return true if delta1 == delta2 */
bool LAdelta_xx_eq(TLAdelta_xx* delta1, TLAdelta_xx* delta2);

/**
   \author Pascal Fontaine
   \brief checks if a delta value is less than or equal to another
   \param[in] delta1 value
   \param[in] delta2 value
   \return true iff delta1 <= delta2 */
bool LAdelta_xx_leq(TLAdelta_xx* delta1, TLAdelta_xx* delta2);

/**
   \author Pascal Fontaine
   \brief checks if a delta value is less than another
   \param[in] delta1 value
   \param[in] delta2 value
   \return true iff delta1 < delta2 */
bool LAdelta_xx_less(TLAdelta_xx* delta1, TLAdelta_xx* delta2);

/**
   \author Pascal Fontaine
   \brief checks if two delta value are not equal
   \param[in] delta1 value
   \param[in] delta2 value
   \return true iff delta1 < delta2 */
bool LAdelta_xx_neq(TLAdelta_xx* delta1, TLAdelta_xx* delta2);

/**
   \author David Deharbe
   \brief compares two delta values
   \param[in] delta1 value
   \param[in] delta2 value
   \return negative if delta1 < delta2, positive if delta1 > delta2,
   zero otherwise */
int LAdelta_xx_cmp(TLAdelta_xx* delta1, TLAdelta_xx* delta2);

/**
   \author Pascal Fontaine
   \brief computes delta0 = delta0 + delta1 * a
   \param[in,out] delta0 value
   \param[in] delta1 value
   \param[in] a value */
void LAdelta_xx_addmult(
	TLAdelta_xx* delta0, TLAdelta_xx* delta1, TLAsigned_xx a);

/**
   \author Pascal Fontaine
   \brief computes delta0 = delta1 - delta2
   \param[out] delta0 value
   \param[in] delta1 value
   \param[in] delta2 value */
void LAdelta_xx_minus(
	TLAdelta_xx* delta0, TLAdelta_xx* delta1, TLAdelta_xx* delta2);

/**
   \author Pascal Fontaine
   \brief computes delta0 = - delta0 / a
   \param[in,out] delta0 value
   \param[in] a value */
void LAdelta_xx_div_opp(TLAdelta_xx* delta0, TLAsigned_xx a);

/**
   \author Pascal Fontaine
   \brief print value of delta
   \param[in] delta */
void LAdelta_xx_print(TLAdelta_xx* delta);

/**
   \author David Deharbe
   \brief computes \f$delta = \lfloor delta \rfloor\f$
   \param[in, out] delta value */
void LAdelta_xx_floor(TLAdelta_xx* delta);

/**
   \author David Deharbe
   \brief computes delta = delta + 1
   \param[in,out] delta value */
void LAdelta_xx_increment(TLAdelta_xx* delta);

/**
   \author David Deharbe
   \brief computes delta = delta - 1
   \param[in,out] delta value */
void LAdelta_xx_decrement(TLAdelta_xx* delta);

/**
   \author David Deharbe
   \param[in,out] delta value */
void LAdelta_xx_normalize(TLAdelta_xx* delta);

#endif
