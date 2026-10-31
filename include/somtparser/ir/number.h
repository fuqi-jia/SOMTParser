/* -*- Header -*-
 *
 * The Numbers
 *
 * Author: Fuqi Jia <jiafq@ios.ac.cn>
 *
 * Copyright (C) 2025 Fuqi Jia
 *
 * Permission is hereby granted, free of charge, to any person obtaining a
 * copy of this software and associated documentation files (the "Software"),
 * to deal in the Software without restriction, including without limitation
 * the rights to use, copy, modify, merge, publish, distribute, sublicense,
 * and/or sell copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
 * DEALINGS IN THE SOFTWARE.
 */

#ifndef NUMBER_HEADER
#define NUMBER_HEADER

#include "somtparser/core/asserting.h"
#include <gmp.h>
#include <gmpxx.h>
#include <mpfr.h>
#include <string>
#include <optional>

namespace SOMTParser {
    class HighPrecisionInteger {
        public:
            // constants
            static HighPrecisionInteger factorial(unsigned long n);
            static HighPrecisionInteger fibonacci(unsigned long n);
            static HighPrecisionInteger gcd(const HighPrecisionInteger& a, const HighPrecisionInteger& b);
            static HighPrecisionInteger lcm(const HighPrecisionInteger& a, const HighPrecisionInteger& b);
            
            // Constructor
            HighPrecisionInteger();
            HighPrecisionInteger(int i);
            HighPrecisionInteger(long i);
            HighPrecisionInteger(unsigned long i);
            HighPrecisionInteger(long long i);
            // On LLP64 (Windows) unsigned long is 32-bit, so a 64-bit unsigned
            // value would otherwise narrow. Ported from the SMTStabilizer fork.
            HighPrecisionInteger(unsigned long long i);
            HighPrecisionInteger(double d);
            HighPrecisionInteger(const std::string& s, int base = 10);
            HighPrecisionInteger(const char* s, int base = 10);
            HighPrecisionInteger(const HighPrecisionInteger& other);
            HighPrecisionInteger(const mpz_t z);
            
            // Assignment operator
            HighPrecisionInteger& operator=(const HighPrecisionInteger& other);
            
            // Destructor (not needed for mpz_class but kept for consistency)
            ~HighPrecisionInteger() = default;
            
            // Basic arithmetic operators
            HighPrecisionInteger operator+(const HighPrecisionInteger& other) const;
            HighPrecisionInteger operator-(const HighPrecisionInteger& other) const;
            HighPrecisionInteger operator-() const;
            HighPrecisionInteger operator*(const HighPrecisionInteger& other) const;
            HighPrecisionInteger operator/(const HighPrecisionInteger& other) const;
            HighPrecisionInteger operator%(const HighPrecisionInteger& other) const;
            // Three integer division conventions, kept apart on purpose. They
            // agree when both operands are positive and disagree otherwise, and
            // every language this project reads picks one:
            //
            //     m    n  | operator/ (trunc) | floorDiv | euclideanDiv
            //    -7    2  |       -3          |    -4    |     -4
            //    -7   -2  |        3          |     3    |      4
            //     7   -2  |       -3          |    -4    |     -3
            //
            // euclideanDiv/euclideanMod are what SMT-LIB's Ints theory defines:
            // they are the unique pair with m = n*q + r and 0 <= r < |n|.
            // floorDiv is NOT that pair -- it agrees only for positive n -- and
            // a comment here used to claim it was, which is how NT_DIV_INT and
            // NT_MOD ended up disagreeing with each other (see
            // src/frontend/simp_parser.cpp).
            HighPrecisionInteger floorDiv(const HighPrecisionInteger& other) const;   // towards -inf
            HighPrecisionInteger euclideanDiv(const HighPrecisionInteger& other) const;
            HighPrecisionInteger euclideanMod(const HighPrecisionInteger& other) const;
            HighPrecisionInteger& operator+=(const HighPrecisionInteger& other);
            HighPrecisionInteger& operator-=(const HighPrecisionInteger& other);
            HighPrecisionInteger& operator*=(const HighPrecisionInteger& other);
            HighPrecisionInteger& operator/=(const HighPrecisionInteger& other);
            HighPrecisionInteger& operator%=(const HighPrecisionInteger& other);
            
            // Increment/decrement operators
            HighPrecisionInteger& operator++();    // Prefix increment
            HighPrecisionInteger operator++(int);  // Postfix increment
            HighPrecisionInteger& operator--();    // Prefix decrement
            HighPrecisionInteger operator--(int);  // Postfix decrement
            
            // Comparison operators
            bool operator==(const HighPrecisionInteger& other) const;
            bool operator!=(const HighPrecisionInteger& other) const;
            bool operator<(const HighPrecisionInteger& other) const;
            bool operator<=(const HighPrecisionInteger& other) const;
            bool operator>(const HighPrecisionInteger& other) const;
            bool operator>=(const HighPrecisionInteger& other) const;
            
            // Bitwise operators
            HighPrecisionInteger operator&(const HighPrecisionInteger& other) const;
            HighPrecisionInteger operator|(const HighPrecisionInteger& other) const;
            HighPrecisionInteger operator^(const HighPrecisionInteger& other) const;
            HighPrecisionInteger operator~() const;
            HighPrecisionInteger operator<<(unsigned long bits) const;
            HighPrecisionInteger operator>>(unsigned long bits) const;
            
            // Other operations
            HighPrecisionInteger abs() const;
            HighPrecisionInteger pow(unsigned long exp) const;
            HighPrecisionInteger sqrt() const;
            HighPrecisionInteger safeSqrt() const;
            HighPrecisionInteger root(unsigned long n) const;
            bool isProbablePrime(int reps = 25) const;
            bool isDivisibleBy(const HighPrecisionInteger& d) const;
            
            // Conversion functions
            std::string toString(int base = 10) const;
            int toInt() const;
            long toLong() const;
            unsigned long toULong() const;
            long long toLongLong() const;
            double toDouble() const;
            
            // Access internal GMP value
            const mpz_class& getMPZ() const;
            mpz_class& getMPZ();
            const mpz_t* get_mpz_t() const;

            // next functions
            HighPrecisionInteger nextBelow() const;
            HighPrecisionInteger nextAbove() const;
            
        private:
            mpz_class value;
    };

    typedef HighPrecisionInteger Integer;

    class HighPrecisionRational {
        public:
            HighPrecisionRational() : value(0) {}
            explicit HighPrecisionRational(const mpq_class& q) : value(q) {}
            explicit HighPrecisionRational(const mpz_class& z) : value(z) {}
            explicit HighPrecisionRational(int i) : value(i) {}
            HighPrecisionRational(const HighPrecisionRational& other) : value(other.value) {}
            explicit HighPrecisionRational(const std::string& s);
            explicit HighPrecisionRational(const char* s);

            // Assignment operator
            HighPrecisionRational& operator=(const HighPrecisionRational& other);

            // Basic arithmetic operators
            HighPrecisionRational operator+(const HighPrecisionRational& other) const;
            HighPrecisionRational operator-(const HighPrecisionRational& other) const;
            HighPrecisionRational operator-() const;
            HighPrecisionRational operator*(const HighPrecisionRational& other) const;
            HighPrecisionRational operator/(const HighPrecisionRational& other) const;

            // Comparison operators
            bool operator==(const HighPrecisionRational& other) const;
            bool operator!=(const HighPrecisionRational& other) const;
            bool operator<(const HighPrecisionRational& other) const;
            bool operator<=(const HighPrecisionRational& other) const;
            bool operator>(const HighPrecisionRational& other) const;
            bool operator>=(const HighPrecisionRational& other) const;

            // Conversion functions
            std::string toString() const;
            double toDouble() const;
            bool isInteger() const;

            // Access internal GMP value
            const mpq_class& getMPQ() const;
            mpq_class& getMPQ();

        private:
            mpq_class value;
    };

    typedef HighPrecisionRational Rational;
    
    class HighPrecisionReal {
        public:
            // constants
            static HighPrecisionReal pi(mpfr_prec_t precision = 128);  // π (pi)
            static HighPrecisionReal e(mpfr_prec_t precision = 128);   // e (natural logarithm base)
            static HighPrecisionReal phi(mpfr_prec_t precision = 128); // φ (golden ratio)
            static HighPrecisionReal ln2(mpfr_prec_t precision = 128); // ln(2)
            static HighPrecisionReal ln10(mpfr_prec_t precision = 128); // ln(10)
            static HighPrecisionReal log2_e(mpfr_prec_t precision = 128); // log₂(e)
            static HighPrecisionReal log10_e(mpfr_prec_t precision = 128); // log₁₀(e)
            static HighPrecisionReal euler(mpfr_prec_t precision = 128); // γ (Euler constant)
            static HighPrecisionReal catalan(mpfr_prec_t precision = 128); // G (Catalan constant)
            static HighPrecisionReal epsilon(mpfr_prec_t precision = 128); // ε (machine epsilon)

            // Constructor
            HighPrecisionReal(mpfr_prec_t precision = 128);
            HighPrecisionReal(int i, mpfr_prec_t precision = 128);
            HighPrecisionReal(const Integer& i, mpfr_prec_t precision = 128);
            HighPrecisionReal(const double& d, mpfr_prec_t precision = 128);
            HighPrecisionReal(const float& f, mpfr_prec_t precision = 128);
            HighPrecisionReal(const std::string& s, mpfr_prec_t precision = 128);
            HighPrecisionReal(const char* s, mpfr_prec_t precision = 128);
            HighPrecisionReal(const mpfr_t& t, mpfr_prec_t precision = 128);
            explicit HighPrecisionReal(const mpq_class& q, mpfr_prec_t precision = 128);
            HighPrecisionReal(const HighPrecisionReal& other);
            
            // Assignment operator
            HighPrecisionReal& operator=(const HighPrecisionReal& other);
            
            // Destructor
            ~HighPrecisionReal();
            
            // Basic arithmetic operators
            HighPrecisionReal operator+(const HighPrecisionReal& other) const;
            HighPrecisionReal operator-(const HighPrecisionReal& other) const;
            HighPrecisionReal operator-() const;
            HighPrecisionReal operator*(const HighPrecisionReal& other) const;
            HighPrecisionReal operator/(const HighPrecisionReal& other) const;
            HighPrecisionReal& operator+=(const HighPrecisionReal& other);
            HighPrecisionReal& operator-=(const HighPrecisionReal& other);
            HighPrecisionReal& operator*=(const HighPrecisionReal& other);
            HighPrecisionReal& operator/=(const HighPrecisionReal& other);
            
            // Comparison operators
            bool operator==(const HighPrecisionReal& other) const;
            bool operator!=(const HighPrecisionReal& other) const;
            bool operator<(const HighPrecisionReal& other) const;
            bool operator<=(const HighPrecisionReal& other) const;
            bool operator>(const HighPrecisionReal& other) const;
            bool operator>=(const HighPrecisionReal& other) const;
            
            // Other operations
            HighPrecisionReal abs() const;
            HighPrecisionReal sqrt() const;
            HighPrecisionReal safeSqrt() const;
            HighPrecisionReal pow(const HighPrecisionReal& exp) const;
            
            // Rounding operations
            HighPrecisionReal ceil() const;
            HighPrecisionReal floor() const;
            HighPrecisionReal round() const;
            
            // Exponential and logarithmic functions
            HighPrecisionReal exp() const;
            HighPrecisionReal ln() const;
            HighPrecisionReal lg() const;
            HighPrecisionReal lb() const;
            HighPrecisionReal log(const HighPrecisionReal& base) const;
            
            // Trigonometric functions
            HighPrecisionReal sin() const;
            HighPrecisionReal cos() const;
            HighPrecisionReal tan() const;
            HighPrecisionReal cot() const;
            HighPrecisionReal sec() const;
            HighPrecisionReal csc() const;
            HighPrecisionReal asin() const;
            HighPrecisionReal acos() const;
            HighPrecisionReal atan() const;
            HighPrecisionReal acot() const;
            HighPrecisionReal asec() const;
            HighPrecisionReal acsc() const;
            static HighPrecisionReal atan2(const HighPrecisionReal& y, const HighPrecisionReal& x);
            
            // Hyperbolic functions
            HighPrecisionReal sinh() const;
            HighPrecisionReal cosh() const;
            HighPrecisionReal tanh() const;
            HighPrecisionReal coth() const;
            HighPrecisionReal sech() const;
            HighPrecisionReal csch() const;
            HighPrecisionReal asinh() const;
            HighPrecisionReal acosh() const;
            HighPrecisionReal atanh() const;
            HighPrecisionReal acoth() const;
            HighPrecisionReal asech() const;
            HighPrecisionReal acsch() const;
            
            // Conversion functions
            std::string toString() const;
            double toDouble() const;
            float toFloat() const;
            int toInt() const;
            long long toLongLong() const;
            Integer toInteger() const;
            // Set and get precision
            void setPrecision(mpfr_prec_t precision);
            mpfr_prec_t getPrecision() const;
            bool isInteger() const;
            
            // Access internal MPFR value
            mpfr_ptr getMPFR();
            mpfr_srcptr getMPFR() const;

            // next functions
            HighPrecisionReal nextBelow() const;
            HighPrecisionReal nextAbove() const;
            bool isInfinity() const;
            bool isNegativeInfinity() const;
            bool isPositiveInfinity() const;

            // NaN
            bool isNaN() const;
            
        private:
            mpfr_t value;
    };

    typedef HighPrecisionReal Real;

    // A unified type that can represent both integers and reals
    class Number {
        public:
            // enum type
            enum Type {
                INT_TYPE,      // Integer
                RATIONAL_TYPE, // Rational (exact)
                REAL_TYPE,     // Real (MPFR, approximate)
                UNKNOWN_TYPE   // Unknown
            };

            // Constant
            // NOTE: `static Number ZERO/ONE/INFINITY;` used to be declared here.
            // None of them had a definition or a single user, so any reference
            // would have been a link error. INFINITY was worse than dead: it is
            // a <cmath> macro, so a translation unit including <cmath> first
            // silently turned the declaration into a function declaration.
            // Use Number(0), Number(1) and Number::infinity() (below) instead.
            static Number pi(size_t precision = 128);
            static Number e(size_t precision = 128);
            static Number phi(size_t precision = 128);
            static Number ln2(size_t precision = 128);
            static Number ln10(size_t precision = 128);
            static Number log2_e(size_t precision = 128);
            static Number log10_e(size_t precision = 128);
            static Number epsilon(size_t precision = 128);

            // Factory methods
            static Number fromApproxDouble(double v);              // Always REAL_TYPE (MPFR approximate)
            static Number fromExactDecimalString(const std::string& s); // Always RATIONAL_TYPE (exact)

            // Constructor
            Number();                                  // Default constructor, create integer 0
            Number(const HighPrecisionInteger& i);     // Construct from integer
            Number(const HighPrecisionRational& r);    // Construct from rational
            Number(const HighPrecisionReal& r);        // Construct from real number
            Number(int i);                             // Construct integer from int
            [[deprecated("Use fromApproxDouble() for approximate contexts only")]]
            Number(double d, bool asInteger = false);  // Construct Real from double
            Number(const std::string& s, bool asInteger = false); // Construct from string (default is real)
            Number(const Number& other);               // Copy constructor


            // Assignment operator
            Number& operator=(const Number& other);

            // Destructor
            ~Number();

            // Type checking
            bool isInteger() const { return type == INT_TYPE || (isRational() && getRational().isInteger()) || (type == REAL_TYPE && getReal().isInteger()); }
            bool isRational() const { return type == RATIONAL_TYPE; }
            bool isReal() const { return type == REAL_TYPE || type == RATIONAL_TYPE; }
            bool isUnknown() const { return type == UNKNOWN_TYPE; }
            Type getType() const { return type; }

            // Get value
            const HighPrecisionInteger& getInteger() const;
            const HighPrecisionRational& getRational() const;
            const HighPrecisionReal& getReal() const;

            // Type conversion
            // Exact integer conversion: only succeeds for INT_TYPE or RATIONAL_TYPE with den==1
            std::optional<HighPrecisionInteger> asIntegerExact() const;
            // Floor integer conversion: SMT to_int semantics (floor towards -inf)
            HighPrecisionInteger floorToInteger() const;
            // Exact rational conversion: throws on REAL_TYPE
            HighPrecisionRational toRationalExact() const;
            // Approximate rational conversion: allows REAL_TYPE via string fallback
            HighPrecisionRational approximateToRational() const;
            HighPrecisionReal toReal(mpfr_prec_t precision = 128) const;

            // Constants
            static Number zero();
            static Number one();
            static Number infinity();
            static Number negativeInfinity();
            static Number positiveInfinity();
            bool isZero() const;
            bool isOne() const;
            bool isInfinity() const;
            bool isNegativeInfinity() const;
            bool isPositiveInfinity() const;

            // Basic operations
            Number operator+(const Number& other) const;
            Number operator-(const Number& other) const;
            Number operator-() const;
            Number operator*(const Number& other) const;
            Number operator/(const Number& other) const;
            Number operator%(const Number& other) const;
            Number& operator+=(const Number& other);
            Number& operator-=(const Number& other);
            Number& operator*=(const Number& other);
            Number& operator/=(const Number& other);
            Number& operator%=(const Number& other);
            
            
            // Comparison operations
            bool operator==(const Number& other) const;
            bool operator!=(const Number& other) const;
            bool operator<(const Number& other) const;
            bool operator<=(const Number& other) const;
            bool operator>(const Number& other) const;
            bool operator>=(const Number& other) const;
            
            // Increment/decrement operators
            Number& operator++();    // Prefix increment
            Number operator++(int);  // Postfix increment
            Number& operator--();    // Prefix decrement
            Number operator--(int);  // Postfix decrement
            
            // Bitwise operators
            Number operator&(const Number& other) const;
            Number operator|(const Number& other) const;
            Number operator^(const Number& other) const;
            Number operator~() const;
            Number operator<<(unsigned long bits) const;
            Number operator>>(unsigned long bits) const;
            
            // Convert to string
            std::string toString() const;
            
            // Mathematical operations
            Number abs() const;
            Number sqrt() const;
            Number safeSqrt() const;
            Number pow(const Number& exp) const;
            
            // Rounding operations
            Number ceil() const;
            Number floor() const;
            Number round() const;
            
            // Exponential and logarithmic functions
            Number exp() const;
            Number ln() const;
            Number lg() const;
            Number lb() const;
            Number log(const Number& base) const;
            
            // Trigonometric functions
            Number sin() const;
            Number cos() const;
            Number tan() const;
            Number cot() const;
            Number sec() const;
            Number csc() const;
            Number asin() const;
            Number acos() const;
            Number atan() const;
            Number acot() const;
            Number asec() const;
            Number acsc() const;
            static Number atan2(const Number& y, const Number& x);
            
            // Hyperbolic functions
            Number sinh() const;
            Number cosh() const;
            Number tanh() const;
            Number coth() const;
            Number sech() const;
            Number csch() const;
            Number asinh() const;
            Number acosh() const;
            Number atanh() const;
            Number acoth() const;
            Number asech() const;
            Number acsch() const;

            // next functions
            Number nextBelow() const;
            Number nextAbove() const;

            // NaN
            bool isNaN() const;

        private:
            Type type;                         // Identify type
            HighPrecisionInteger intValue;     // Integer value
            HighPrecisionRational ratValue;    // Rational value
            HighPrecisionReal realValue;       // Real value
    };
}

#endif

