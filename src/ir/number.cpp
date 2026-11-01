/* -*- Source -*-
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

#include "somtparser/ir/number.h"
#include <stdexcept>
#include <string>
#include <cmath>
#include <climits> // For LLONG_MAX and LLONG_MIN

namespace SOMTParser {

// -------------HighPrecisionReal-------------
// Constants
HighPrecisionReal HighPrecisionReal::pi(mpfr_prec_t precision) {
    HighPrecisionReal result(precision);
    mpfr_const_pi(result.value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::e(mpfr_prec_t precision) {
    HighPrecisionReal result(precision);
    // use exp(1) to calculate e
    mpfr_set_ui(result.value, 1, MPFR_RNDN);
    mpfr_exp(result.value, result.value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::phi(mpfr_prec_t precision) {
    HighPrecisionReal result(precision);
    // φ = (1 + sqrt(5)) / 2
    HighPrecisionReal five(5, precision);
    HighPrecisionReal sqrt5 = five.sqrt();
    HighPrecisionReal one(1, precision);
    mpfr_add(result.value, one.value, sqrt5.value, MPFR_RNDN);
    mpfr_div_ui(result.value, result.value, 2, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::ln2(mpfr_prec_t precision) {
    HighPrecisionReal result(precision);
    mpfr_const_log2(result.value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::ln10(mpfr_prec_t precision) {
    HighPrecisionReal result(precision);
    HighPrecisionReal ten(10, precision);
    mpfr_log(result.value, ten.value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::log2_e(mpfr_prec_t precision) {
    HighPrecisionReal result(precision);
    // log₂(e) = 1/ln(2)
    mpfr_const_log2(result.value, MPFR_RNDN);
    mpfr_ui_div(result.value, 1, result.value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::log10_e(mpfr_prec_t precision) {
    HighPrecisionReal result(precision);
    // log₁₀(e) = 1/ln(10)
    HighPrecisionReal ten(10, precision);
    mpfr_log(result.value, ten.value, MPFR_RNDN);
    mpfr_ui_div(result.value, 1, result.value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::euler(mpfr_prec_t precision) {
    HighPrecisionReal result(precision);
    mpfr_const_euler(result.value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::catalan(mpfr_prec_t precision) {
    HighPrecisionReal result(precision);
    mpfr_const_catalan(result.value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::epsilon(mpfr_prec_t precision) {
    mpfr_t one, next, eps;
    mpfr_init2(one, precision);
    mpfr_init2(next, precision);
    mpfr_init2(eps, precision);

    mpfr_set_ui(one, 1, MPFR_RNDN);       // one = 1
    mpfr_set(next, one, MPFR_RNDN);       // next = 1
    mpfr_nextabove(next);                  // next = next representable number > 1
    mpfr_sub(eps, next, one, MPFR_RNDN);  // eps = next - 1
    return HighPrecisionReal(eps);
}

// Constructor
HighPrecisionReal::HighPrecisionReal(mpfr_prec_t precision) {
    mpfr_init2(value, precision);
    mpfr_set_zero(value, 1); // Initialize to +0
}

HighPrecisionReal::HighPrecisionReal(int i, mpfr_prec_t precision) {
    mpfr_init2(value, precision);
    mpfr_set_si(value, i, MPFR_RNDN);
}

HighPrecisionReal::HighPrecisionReal(const Integer& i, mpfr_prec_t precision) {
    mpfr_init2(value, precision);
    mpfr_set_z(value, i.getMPZ().get_mpz_t(), MPFR_RNDN);
}

HighPrecisionReal::HighPrecisionReal(const double& d, mpfr_prec_t precision) {
    mpfr_init2(value, precision);
    mpfr_set_d(value, d, MPFR_RNDN);
}

HighPrecisionReal::HighPrecisionReal(const float& f, mpfr_prec_t precision) {
    mpfr_init2(value, precision);
    mpfr_set_flt(value, f, MPFR_RNDN);
}

HighPrecisionReal::HighPrecisionReal(const std::string& s, mpfr_prec_t precision) {
    mpfr_init2(value, precision);  // Initialize value
    
    if (mpfr_set_str(value, s.c_str(), 10, MPFR_RNDN) != 0) {
        mpfr_clear(value);
        throw std::invalid_argument("Cannot convert string to high precision real number");
    }
}

HighPrecisionReal::HighPrecisionReal(const char* s, mpfr_prec_t precision) {
    mpfr_init2(value, precision);  // Initialize value
    
    if (mpfr_set_str(value, s, 10, MPFR_RNDN) != 0) {
        mpfr_clear(value);
        throw std::invalid_argument("Cannot convert string to high precision real number");
    }
}

HighPrecisionReal::HighPrecisionReal(const mpfr_t& t, mpfr_prec_t precision) {
    mpfr_init2(value, precision);
    mpfr_set(value, t, MPFR_RNDN);
}

HighPrecisionReal::HighPrecisionReal(const HighPrecisionReal& other) {
    mpfr_init2(value, mpfr_get_prec(other.value));
    mpfr_set(value, other.value, MPFR_RNDN);
}

// Assignment operator
HighPrecisionReal& HighPrecisionReal::operator=(const HighPrecisionReal& other) {
    if (this != &other) {
        // If precision is different, reinitialize
        if (mpfr_get_prec(value) != mpfr_get_prec(other.value)) {
            mpfr_clear(value);
            mpfr_init2(value, mpfr_get_prec(other.value));
        }
        mpfr_set(value, other.value, MPFR_RNDN);
    }
    return *this;
}

// Destructor
HighPrecisionReal::~HighPrecisionReal() {
    mpfr_clear(value);
}

// Basic arithmetic operators
HighPrecisionReal HighPrecisionReal::operator+(const HighPrecisionReal& other) const {
    HighPrecisionReal result(std::max(mpfr_get_prec(value), mpfr_get_prec(other.value)));
    mpfr_add(result.value, value, other.value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::operator-(const HighPrecisionReal& other) const {
    HighPrecisionReal result(std::max(mpfr_get_prec(value), mpfr_get_prec(other.value)));
    mpfr_sub(result.value, value, other.value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::operator-() const {
    HighPrecisionReal result(mpfr_get_prec(value));
    mpfr_neg(result.value, value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::operator*(const HighPrecisionReal& other) const {
    HighPrecisionReal result(std::max(mpfr_get_prec(value), mpfr_get_prec(other.value)));
    mpfr_mul(result.value, value, other.value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::operator/(const HighPrecisionReal& other) const {
    HighPrecisionReal result(std::max(mpfr_get_prec(value), mpfr_get_prec(other.value)));
    mpfr_div(result.value, value, other.value, MPFR_RNDN);
    return result;
}

HighPrecisionReal& HighPrecisionReal::operator+=(const HighPrecisionReal& other) {
    mpfr_add(value, value, other.value, MPFR_RNDN);
    return *this;
}

HighPrecisionReal& HighPrecisionReal::operator-=(const HighPrecisionReal& other) {
    mpfr_sub(value, value, other.value, MPFR_RNDN);
    return *this;
}

HighPrecisionReal& HighPrecisionReal::operator*=(const HighPrecisionReal& other) {
    mpfr_mul(value, value, other.value, MPFR_RNDN);
    return *this;
}

HighPrecisionReal& HighPrecisionReal::operator/=(const HighPrecisionReal& other) {
    mpfr_div(value, value, other.value, MPFR_RNDN);
    return *this;
}

// Comparison operators
bool HighPrecisionReal::operator==(const HighPrecisionReal& other) const {
    return mpfr_equal_p(value, other.value) != 0;
}

bool HighPrecisionReal::operator!=(const HighPrecisionReal& other) const {
    return !(*this == other);
}

bool HighPrecisionReal::operator<(const HighPrecisionReal& other) const {
    return mpfr_less_p(value, other.value) != 0;
}

bool HighPrecisionReal::operator<=(const HighPrecisionReal& other) const {
    return mpfr_lessequal_p(value, other.value) != 0;
}

bool HighPrecisionReal::operator>(const HighPrecisionReal& other) const {
    return mpfr_greater_p(value, other.value) != 0;
}

bool HighPrecisionReal::operator>=(const HighPrecisionReal& other) const {
    return mpfr_greaterequal_p(value, other.value) != 0;
}

// Other operations
HighPrecisionReal HighPrecisionReal::abs() const {
    HighPrecisionReal result(mpfr_get_prec(value));
    mpfr_abs(result.value, value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::sqrt() const {
    if (*this < HighPrecisionReal(0)) {
        throw std::domain_error("Cannot compute square root of a negative number");
    }
    HighPrecisionReal result(mpfr_get_prec(value));
    mpfr_sqrt(result.value, value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::safeSqrt() const {
    if (*this < HighPrecisionReal(0)) {
        return HighPrecisionReal(0);
    }
    return sqrt();
}

HighPrecisionReal HighPrecisionReal::pow(const HighPrecisionReal& exp) const {
    HighPrecisionReal result(std::max(mpfr_get_prec(value), mpfr_get_prec(exp.value)));
    mpfr_pow(result.value, value, exp.value, MPFR_RNDN);
    return result;
}

// Rounding operations
HighPrecisionReal HighPrecisionReal::ceil() const {
    HighPrecisionReal result(mpfr_get_prec(value));
    mpfr_ceil(result.value, value);
    return result;
}

HighPrecisionReal HighPrecisionReal::floor() const {
    HighPrecisionReal result(mpfr_get_prec(value));
    mpfr_floor(result.value, value);
    return result;
}

HighPrecisionReal HighPrecisionReal::round() const {
    HighPrecisionReal result(mpfr_get_prec(value));
    mpfr_round(result.value, value);
    return result;
}

// Exponential and logarithmic functions
HighPrecisionReal HighPrecisionReal::exp() const {
    HighPrecisionReal result(mpfr_get_prec(value));
    mpfr_exp(result.value, value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::ln() const {
    if (*this <= HighPrecisionReal(0)) {
        throw std::domain_error("Cannot compute logarithm of a non-positive number");
    }
    HighPrecisionReal result(mpfr_get_prec(value));
    mpfr_log(result.value, value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::lg() const {
    if (*this <= HighPrecisionReal(0)) {
        throw std::domain_error("Cannot compute logarithm of a non-positive number");
    }
    HighPrecisionReal result(mpfr_get_prec(value));
    mpfr_log10(result.value, value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::lb() const {
    if (*this <= HighPrecisionReal(0)) {
        throw std::domain_error("Cannot compute logarithm of a non-positive number");
    }
    HighPrecisionReal result(mpfr_get_prec(value));
    mpfr_log2(result.value, value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::log(const HighPrecisionReal& base) const {
    if (*this <= HighPrecisionReal(0) || base <= HighPrecisionReal(0) || base == HighPrecisionReal(1)) {
        throw std::domain_error("Invalid arguments for logarithm");
    }
    HighPrecisionReal result = ln();
    HighPrecisionReal baseLog = base.ln();
    mpfr_div(result.value, result.value, baseLog.value, MPFR_RNDN);
    return result;
}

// Trigonometric functions
HighPrecisionReal HighPrecisionReal::sin() const {
    HighPrecisionReal result(mpfr_get_prec(value));
    mpfr_sin(result.value, value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::cos() const {
    HighPrecisionReal result(mpfr_get_prec(value));
    mpfr_cos(result.value, value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::tan() const {
    HighPrecisionReal result(mpfr_get_prec(value));
    mpfr_tan(result.value, value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::cot() const {
    HighPrecisionReal result(mpfr_get_prec(value));
    mpfr_cot(result.value, value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::sec() const {
    HighPrecisionReal result(mpfr_get_prec(value));
    mpfr_sec(result.value, value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::csc() const {
    HighPrecisionReal result(mpfr_get_prec(value));
    mpfr_csc(result.value, value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::asin() const {
    if (*this < HighPrecisionReal(-1) || *this > HighPrecisionReal(1)) {
        throw std::domain_error("Argument for asin must be in range [-1, 1]");
    }
    HighPrecisionReal result(mpfr_get_prec(value));
    mpfr_asin(result.value, value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::acos() const {
    if (*this < HighPrecisionReal(-1) || *this > HighPrecisionReal(1)) {
        throw std::domain_error("Argument for acos must be in range [-1, 1]");
    }
    HighPrecisionReal result(mpfr_get_prec(value));
    mpfr_acos(result.value, value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::atan() const {
    HighPrecisionReal result(mpfr_get_prec(value));
    mpfr_atan(result.value, value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::acot() const {
    // acot(x) = π/2 - atan(x)
    HighPrecisionReal result(mpfr_get_prec(value));
    HighPrecisionReal pi_half = pi(mpfr_get_prec(value)) / HighPrecisionReal(2);
    HighPrecisionReal atan_val = atan();
    mpfr_sub(result.value, pi_half.value, atan_val.value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::asec() const {
    // asec(x) = acos(1/x)
    if (*this == HighPrecisionReal(0)) {
        throw std::domain_error("Argument for asec cannot be 0");
    }
    HighPrecisionReal reciprocal(mpfr_get_prec(value));
    mpfr_ui_div(reciprocal.value, 1, value, MPFR_RNDN);
    return reciprocal.acos();
}

HighPrecisionReal HighPrecisionReal::acsc() const {
    // acsc(x) = asin(1/x)
    if (*this == HighPrecisionReal(0)) {
        throw std::domain_error("Argument for acsc cannot be 0");
    }
    HighPrecisionReal reciprocal(mpfr_get_prec(value));
    mpfr_ui_div(reciprocal.value, 1, value, MPFR_RNDN);
    return reciprocal.asin();
}

HighPrecisionReal HighPrecisionReal::atan2(const HighPrecisionReal& y, const HighPrecisionReal& x) {
    mpfr_prec_t precision = std::max(mpfr_get_prec(y.value), mpfr_get_prec(x.value));
    HighPrecisionReal result(precision);
    mpfr_atan2(result.value, y.value, x.value, MPFR_RNDN);
    return result;
}

// Hyperbolic functions
HighPrecisionReal HighPrecisionReal::sinh() const {
    HighPrecisionReal result(mpfr_get_prec(value));
    mpfr_sinh(result.value, value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::cosh() const {
    HighPrecisionReal result(mpfr_get_prec(value));
    mpfr_cosh(result.value, value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::tanh() const {
    HighPrecisionReal result(mpfr_get_prec(value));
    mpfr_tanh(result.value, value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::coth() const {
    HighPrecisionReal result(mpfr_get_prec(value));
    mpfr_coth(result.value, value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::sech() const {
    HighPrecisionReal result(mpfr_get_prec(value));
    mpfr_sech(result.value, value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::csch() const {
    HighPrecisionReal result(mpfr_get_prec(value));
    mpfr_csch(result.value, value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::asinh() const {
    HighPrecisionReal result(mpfr_get_prec(value));
    mpfr_asinh(result.value, value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::acosh() const {
    if (*this < HighPrecisionReal(1)) {
        throw std::domain_error("Argument for acosh must be >= 1");
    }
    HighPrecisionReal result(mpfr_get_prec(value));
    mpfr_acosh(result.value, value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::atanh() const {
    if (*this <= HighPrecisionReal(-1) || *this >= HighPrecisionReal(1)) {
        throw std::domain_error("Argument for atanh must be in range (-1, 1)");
    }
    HighPrecisionReal result(mpfr_get_prec(value));
    mpfr_atanh(result.value, value, MPFR_RNDN);
    return result;
}

HighPrecisionReal HighPrecisionReal::acoth() const {
    // acoth(x) = atanh(1/x)
    if (*this >= HighPrecisionReal(-1) && *this <= HighPrecisionReal(1)) {
        throw std::domain_error("Argument for acoth must be outside range [-1, 1]");
    }
    HighPrecisionReal reciprocal(mpfr_get_prec(value));
    mpfr_ui_div(reciprocal.value, 1, value, MPFR_RNDN);
    return reciprocal.atanh();
}

HighPrecisionReal HighPrecisionReal::asech() const {
    if (*this <= HighPrecisionReal(0) || *this > HighPrecisionReal(1)) {
        throw std::domain_error("Argument for asech must be in range (0, 1]");
    }
    // asech(x) = acosh(1/x)
    HighPrecisionReal reciprocal(mpfr_get_prec(value));
    mpfr_ui_div(reciprocal.value, 1, value, MPFR_RNDN);
    return reciprocal.acosh();
}

HighPrecisionReal HighPrecisionReal::acsch() const {
    if (*this == HighPrecisionReal(0)) {
        throw std::domain_error("Argument for acsch cannot be 0");
    }
    // acsch(x) = asinh(1/x)
    HighPrecisionReal reciprocal(mpfr_get_prec(value));
    mpfr_ui_div(reciprocal.value, 1, value, MPFR_RNDN);
    return reciprocal.asinh();
}

bool HighPrecisionReal::isNaN() const {
    return mpfr_nan_p(value) != 0;
}

// Conversion functions
std::string HighPrecisionReal::toString() const {
    // for integer, output decimal directly, without scientific notation;
    // for other cases, output at most 17 significant digits, unless the exponent is too large.

    // 1. NaN / Inf
    if(mpfr_nan_p(value)) return "NaN";
    if(mpfr_inf_p(value)) return mpfr_sgn(value) < 0 ? "-inf" : "inf";

    // 2. integer: %.0Rf
    char *buf = nullptr;
    if(mpfr_integer_p(value)){
        mpfr_asprintf(&buf, "%.0Rf", value);  // No fractional part
    } else {
        // 3. non-integer: output at most 17 significant digits, if the exponent is in [-6,6] use f, otherwise use g
        // get the exponent
        mpfr_exp_t exp10;
        mpfr_get_str(nullptr, &exp10, 10, 0, value, MPFR_RNDN);
        if(exp10 >= -6 && exp10 <= 6){
            // fixed decimal format, keep enough significant digits
            mpfr_asprintf(&buf, "%.17Rf", value);
            // remove trailing zeros and decimal point
            std::string tmp(buf);
            mpfr_free_str(buf);
            // remove trailing zeros
            while(tmp.size()>1 && tmp.back()=='0') tmp.pop_back();
            if(!tmp.empty() && tmp.back()=='.') tmp.pop_back();
            return tmp;
        } else {
            mpfr_asprintf(&buf, "%.17Rg", value); // scientific notation, but control significant digits
        }
    }
    std::string s(buf);
    mpfr_free_str(buf);
    return s;
}

double HighPrecisionReal::toDouble() const {
    std::string str = toString();
    return std::stod(str);
}

float HighPrecisionReal::toFloat() const {
    std::string str = toString();
    return std::stof(str);
}

int HighPrecisionReal::toInt() const {
    return mpfr_get_si(value, MPFR_RNDN);
}

Integer HighPrecisionReal::toInteger() const {
    mpz_t z;
    mpz_init(z);
    mpfr_get_z(z, value, MPFR_RNDN);
    Integer result(z);
    mpz_clear(z);
    return result;
}

long long HighPrecisionReal::toLongLong() const {
    // MPFR doesn't have a direct mpfr_get_ll function, so we'll use a workaround
    // First convert to integer, then to long long
    mpz_t z;
    mpz_init(z);
    mpfr_get_z(z, value, MPFR_RNDN);
    
    // Get the value as a long long
    long long result;
    if (mpz_fits_slong_p(z)) {
        result = mpz_get_si(z);
    } else {
        // Handle values that are too large
        if (mpz_sgn(z) >= 0) {
            result = LLONG_MAX; // Maximum long long value
        } else {
            result = LLONG_MIN; // Minimum long long value
        }
    }
    
    mpz_clear(z);
    return result;
}

// Set and get precision
void HighPrecisionReal::setPrecision(mpfr_prec_t precision) {
    mpfr_prec_round(value, precision, MPFR_RNDN);
}

mpfr_prec_t HighPrecisionReal::getPrecision() const {
    return mpfr_get_prec(value);
}

bool HighPrecisionReal::isInteger() const {
    return mpfr_integer_p(value);
}

// Access internal MPFR value
mpfr_ptr HighPrecisionReal::getMPFR() {
    return value;
}

mpfr_srcptr HighPrecisionReal::getMPFR() const {
    return value;
}

HighPrecisionReal HighPrecisionReal::nextBelow() const {
    HighPrecisionReal result(mpfr_get_prec(value));
    mpfr_set(result.value, value, MPFR_RNDN);
    mpfr_nextbelow(result.value);
    return result;
}

HighPrecisionReal HighPrecisionReal::nextAbove() const {
    HighPrecisionReal result(mpfr_get_prec(value));
    mpfr_set(result.value, value, MPFR_RNDN);
    mpfr_nextabove(result.value);
    return result;
}

bool HighPrecisionReal::isInfinity() const {
    return mpfr_inf_p(value) != 0;
}

bool HighPrecisionReal::isNegativeInfinity() const {
    return mpfr_inf_p(value) != 0 && mpfr_sgn(value) < 0;
}

bool HighPrecisionReal::isPositiveInfinity() const {
    return mpfr_inf_p(value) != 0 && mpfr_sgn(value) > 0;
}

// -------------HighPrecisionInteger-------------
HighPrecisionInteger::HighPrecisionInteger(const mpz_t z) {
    mpz_set(value.get_mpz_t(), z);
}

const mpz_t* HighPrecisionInteger::get_mpz_t() const {
    return (const mpz_t*)value.get_mpz_t();
}

// Static methods
HighPrecisionInteger HighPrecisionInteger::factorial(unsigned long n) {
    HighPrecisionInteger result(1);
    for (unsigned long i = 2; i <= n; ++i) {
        result *= HighPrecisionInteger(i);
    }
    return result;
}

HighPrecisionInteger HighPrecisionInteger::fibonacci(unsigned long n) {
    if (n <= 1) return HighPrecisionInteger(n);
    HighPrecisionInteger a(0);
    HighPrecisionInteger b(1);
    HighPrecisionInteger c;
    for (unsigned long i = 2; i <= n; ++i) {
        c = a + b;
        a = b;
        b = c;
    }
    return b;
}

HighPrecisionInteger HighPrecisionInteger::gcd(const HighPrecisionInteger& a, const HighPrecisionInteger& b) {
    HighPrecisionInteger result;
    mpz_gcd(result.value.get_mpz_t(), a.value.get_mpz_t(), b.value.get_mpz_t());
    return result;
}

HighPrecisionInteger HighPrecisionInteger::lcm(const HighPrecisionInteger& a, const HighPrecisionInteger& b) {
    HighPrecisionInteger result;
    mpz_lcm(result.value.get_mpz_t(), a.value.get_mpz_t(), b.value.get_mpz_t());
    return result;
}

// Constructors
HighPrecisionInteger::HighPrecisionInteger() : value(0) {}

HighPrecisionInteger::HighPrecisionInteger(int i) : value(i) {}

HighPrecisionInteger::HighPrecisionInteger(long i) : value(i) {}

HighPrecisionInteger::HighPrecisionInteger(unsigned long i) : value(i) {}

// A signed long long also exceeds long on LLP64 platforms.
HighPrecisionInteger::HighPrecisionInteger(long long i) : value(std::to_string(i)) {}

// mpz_class has no unsigned long long constructor, so go through the decimal
// string to stay exact on platforms where unsigned long is narrower.
HighPrecisionInteger::HighPrecisionInteger(unsigned long long i) : value(std::to_string(i)) {}

HighPrecisionInteger::HighPrecisionInteger(double d) : value(d) {}

HighPrecisionInteger::HighPrecisionInteger(const std::string& s, int base) {
    try {
        value = mpz_class(s, base);
    } catch (const std::exception& e) {
        throw std::invalid_argument("Cannot convert string to high precision integer");
    }
}

HighPrecisionInteger::HighPrecisionInteger(const char* s, int base) {
    try {
        value = mpz_class(s, base);
    } catch (const std::exception& e) {
        throw std::invalid_argument("Cannot convert string to high precision integer");
    }
}

HighPrecisionInteger::HighPrecisionInteger(const HighPrecisionInteger& other) : value(other.value) {}

// Assignment operator
HighPrecisionInteger& HighPrecisionInteger::operator=(const HighPrecisionInteger& other) {
    if (this != &other) {
        value = other.value;
    }
    return *this;
}

// Basic arithmetic operators
HighPrecisionInteger HighPrecisionInteger::operator+(const HighPrecisionInteger& other) const {
    HighPrecisionInteger result;
    result.value = value + other.value;
    return result;
}

HighPrecisionInteger HighPrecisionInteger::operator-(const HighPrecisionInteger& other) const {
    HighPrecisionInteger result;
    result.value = value - other.value;
    return result;
}

HighPrecisionInteger HighPrecisionInteger::operator-() const {
    HighPrecisionInteger result;
    result.value = -value;
    return result;
}

HighPrecisionInteger HighPrecisionInteger::operator*(const HighPrecisionInteger& other) const {
    HighPrecisionInteger result;
    result.value = value * other.value;
    return result;
}

HighPrecisionInteger HighPrecisionInteger::operator/(const HighPrecisionInteger& other) const {
    if (other.value == 0) {
        throw std::domain_error("Division by zero");
    }
    HighPrecisionInteger result;
    result.value = value / other.value;
    return result;
}

HighPrecisionInteger HighPrecisionInteger::operator%(const HighPrecisionInteger& other) const {
    if (other.value == 0) {
        throw std::domain_error("Modulo by zero");
    }
    HighPrecisionInteger result;
    result.value = value % other.value;
    return result;
}

HighPrecisionInteger HighPrecisionInteger::floorDiv(const HighPrecisionInteger& other) const {
    if (other.value == 0) {
        throw std::domain_error("Division by zero");
    }
    mpz_class q;
    mpz_fdiv_q(q.get_mpz_t(), value.get_mpz_t(), other.value.get_mpz_t());
    return HighPrecisionInteger(q.get_str());
}

// Euclidean division, as SMT-LIB's Ints theory defines div and mod: the unique
// q, r with m = n*q + r and 0 <= r < |n|.
//
// GMP has no Euclidean rounding mode, but it falls out of the two it does have:
// the remainder of a floor division is non-negative exactly when the divisor is
// positive, and the remainder of a ceiling division is non-negative exactly
// when the divisor is negative. So pick by the sign of the divisor.
HighPrecisionInteger HighPrecisionInteger::euclideanDiv(const HighPrecisionInteger& other) const {
    if (other.value == 0) {
        throw std::domain_error("Division by zero");
    }
    mpz_class q;
    if (other.value > 0) {
        mpz_fdiv_q(q.get_mpz_t(), value.get_mpz_t(), other.value.get_mpz_t());
    } else {
        mpz_cdiv_q(q.get_mpz_t(), value.get_mpz_t(), other.value.get_mpz_t());
    }
    return HighPrecisionInteger(q.get_str());
}

HighPrecisionInteger HighPrecisionInteger::euclideanMod(const HighPrecisionInteger& other) const {
    if (other.value == 0) {
        throw std::domain_error("Modulo by zero");
    }
    mpz_class r;
    if (other.value > 0) {
        mpz_fdiv_r(r.get_mpz_t(), value.get_mpz_t(), other.value.get_mpz_t());
    } else {
        mpz_cdiv_r(r.get_mpz_t(), value.get_mpz_t(), other.value.get_mpz_t());
    }
    return HighPrecisionInteger(r.get_str());
}

HighPrecisionInteger& HighPrecisionInteger::operator+=(const HighPrecisionInteger& other) {
    value += other.value;
    return *this;
}

HighPrecisionInteger& HighPrecisionInteger::operator-=(const HighPrecisionInteger& other) {
    value -= other.value;
    return *this;
}

HighPrecisionInteger& HighPrecisionInteger::operator*=(const HighPrecisionInteger& other) {
    value *= other.value;
    return *this;
}

HighPrecisionInteger& HighPrecisionInteger::operator/=(const HighPrecisionInteger& other) {
    if (other.value == 0) {
        throw std::domain_error("Division by zero");
    }
    value /= other.value;
    return *this;
}

HighPrecisionInteger& HighPrecisionInteger::operator%=(const HighPrecisionInteger& other) {
    if (other.value == 0) {
        throw std::domain_error("Modulo by zero");
    }
    value %= other.value;
    return *this;
}

// Increment/decrement operators
HighPrecisionInteger& HighPrecisionInteger::operator++() {
    ++value;
    return *this;
}

HighPrecisionInteger HighPrecisionInteger::operator++(int) {
    HighPrecisionInteger temp(*this);
    ++value;
    return temp;
}

HighPrecisionInteger& HighPrecisionInteger::operator--() {
    --value;
    return *this;
}

HighPrecisionInteger HighPrecisionInteger::operator--(int) {
    HighPrecisionInteger temp(*this);
    --value;
    return temp;
}

// Comparison operators
bool HighPrecisionInteger::operator==(const HighPrecisionInteger& other) const {
    return value == other.value;
}

bool HighPrecisionInteger::operator!=(const HighPrecisionInteger& other) const {
    return value != other.value;
}

bool HighPrecisionInteger::operator<(const HighPrecisionInteger& other) const {
    return value < other.value;
}

bool HighPrecisionInteger::operator<=(const HighPrecisionInteger& other) const {
    return value <= other.value;
}

bool HighPrecisionInteger::operator>(const HighPrecisionInteger& other) const {
    return value > other.value;
}

bool HighPrecisionInteger::operator>=(const HighPrecisionInteger& other) const {
    return value >= other.value;
}

// Bitwise operators
HighPrecisionInteger HighPrecisionInteger::operator&(const HighPrecisionInteger& other) const {
    HighPrecisionInteger result;
    mpz_and(result.value.get_mpz_t(), value.get_mpz_t(), other.value.get_mpz_t());
    return result;
}

HighPrecisionInteger HighPrecisionInteger::operator|(const HighPrecisionInteger& other) const {
    HighPrecisionInteger result;
    mpz_ior(result.value.get_mpz_t(), value.get_mpz_t(), other.value.get_mpz_t());
    return result;
}

HighPrecisionInteger HighPrecisionInteger::operator^(const HighPrecisionInteger& other) const {
    HighPrecisionInteger result;
    mpz_xor(result.value.get_mpz_t(), value.get_mpz_t(), other.value.get_mpz_t());
    return result;
}

HighPrecisionInteger HighPrecisionInteger::operator~() const {
    HighPrecisionInteger result;
    mpz_com(result.value.get_mpz_t(), value.get_mpz_t());
    return result;
}

HighPrecisionInteger HighPrecisionInteger::operator<<(unsigned long bits) const {
    HighPrecisionInteger result;
    mpz_mul_2exp(result.value.get_mpz_t(), value.get_mpz_t(), bits);
    return result;
}

HighPrecisionInteger HighPrecisionInteger::operator>>(unsigned long bits) const {
    HighPrecisionInteger result;
    mpz_fdiv_q_2exp(result.value.get_mpz_t(), value.get_mpz_t(), bits);
    return result;
}

// Other operations
HighPrecisionInteger HighPrecisionInteger::abs() const {
    HighPrecisionInteger result;
    mpz_abs(result.value.get_mpz_t(), value.get_mpz_t());
    return result;
}

HighPrecisionInteger HighPrecisionInteger::pow(unsigned long exp) const {
    HighPrecisionInteger result;
    mpz_pow_ui(result.value.get_mpz_t(), value.get_mpz_t(), exp);
    return result;
}

HighPrecisionInteger HighPrecisionInteger::sqrt() const {
    if (*this < HighPrecisionInteger(0)) {
        throw std::domain_error("Cannot compute square root of a negative number");
    }
    HighPrecisionInteger result;
    mpz_sqrt(result.value.get_mpz_t(), value.get_mpz_t());
    return result;
}

HighPrecisionInteger HighPrecisionInteger::safeSqrt() const {
    if (*this < HighPrecisionInteger(0)) {
        return HighPrecisionInteger(0);
    }
    HighPrecisionInteger result;
    mpz_sqrt(result.value.get_mpz_t(), value.get_mpz_t());
    return result;
}
HighPrecisionInteger HighPrecisionInteger::root(unsigned long n) const {
    if (n == 0) {
        throw std::domain_error("Cannot compute zeroth root");
    }
    if (*this < HighPrecisionInteger(0) && n % 2 == 0) {
        throw std::domain_error("Cannot compute even root of a negative number");
    }
    HighPrecisionInteger result;
    mpz_root(result.value.get_mpz_t(), value.get_mpz_t(), n);
    return result;
}

bool HighPrecisionInteger::isProbablePrime(int reps) const {
    return mpz_probab_prime_p(value.get_mpz_t(), reps) > 0;
}

bool HighPrecisionInteger::isDivisibleBy(const HighPrecisionInteger& d) const {
    if (d.value == 0) {
        throw std::domain_error("Cannot check divisibility by zero");
    }
    return mpz_divisible_p(value.get_mpz_t(), d.value.get_mpz_t()) != 0;
}

// Conversion functions
std::string HighPrecisionInteger::toString(int base) const {
    if (base < 2 || base > 62) {
        throw std::invalid_argument("Base must be between 2 and 62");
    }
    char* str = mpz_get_str(nullptr, base, value.get_mpz_t());
    std::string result(str);
    free(str);
    return result;
}

int HighPrecisionInteger::toInt() const {
    if (value > INT_MAX || value < INT_MIN) {
        throw std::overflow_error("Value does not fit in int");
    }
    return value.get_si();
}

long HighPrecisionInteger::toLong() const {
    if (!mpz_fits_slong_p(value.get_mpz_t())) {
        throw std::overflow_error("Value does not fit in long");
    }
    return value.get_si();
}

unsigned long HighPrecisionInteger::toULong() const {
    if (value < 0 || !mpz_fits_ulong_p(value.get_mpz_t())) {
        throw std::overflow_error("Value does not fit in unsigned long");
    }
    return value.get_ui();
}

long long HighPrecisionInteger::toLongLong() const {
    // GMP doesn't directly support conversion to long long
    // We'll use string conversion for very large numbers
    if (mpz_fits_slong_p(value.get_mpz_t())) {
        return value.get_si();
    } else {
        try {
            return std::stoll(toString(10));
        } catch (const std::exception& e) {
            throw std::overflow_error("Value does not fit in long long");
        }
    }
}

double HighPrecisionInteger::toDouble() const {
    return value.get_d();
}

// Access internal GMP value
const mpz_class& HighPrecisionInteger::getMPZ() const {
    return value;
}

mpz_class& HighPrecisionInteger::getMPZ() {
    return value;
}

HighPrecisionInteger HighPrecisionInteger::nextBelow() const {
    HighPrecisionInteger result;
    result.value = value - 1;
    return result;
}

HighPrecisionInteger HighPrecisionInteger::nextAbove() const {
    HighPrecisionInteger result;
    result.value = value + 1;
    return result;
}

// -------------HighPrecisionRational-------------
HighPrecisionRational::HighPrecisionRational(const std::string& s) {
    size_t slashPos = s.find('/');
    if (slashPos != std::string::npos) {
        // a/b format
        std::string numStr = s.substr(0, slashPos);
        std::string denStr = s.substr(slashPos + 1);
        mpz_class num(numStr);
        mpz_class den(denStr);
        value = mpq_class(num, den);
        value.canonicalize();
        return;
    }

    size_t dotPos = s.find('.');
    if (dotPos == std::string::npos) {
        // pure integer
        value = mpq_class(s);
        return;
    }

    std::string intPart = s.substr(0, dotPos);
    std::string fracPart = s.substr(dotPos + 1);

    // strip trailing zeros
    while (!fracPart.empty() && fracPart.back() == '0') {
        fracPart.pop_back();
    }

    if (fracPart.empty()) {
        value = mpq_class(intPart);
        return;
    }

    // e.g. "59.01938237" -> 5901938237 / 1000000000
    // Use base=10 explicitly to prevent octal interpretation of leading zeros
    mpz_class num(intPart + fracPart, 10);
    mpz_class den(1);
    for (size_t i = 0; i < fracPart.length(); ++i) {
        den *= 10;
    }

    value = mpq_class(num, den);
    value.canonicalize();
}

HighPrecisionRational::HighPrecisionRational(const char* s)
    : HighPrecisionRational(std::string(s)) {}

HighPrecisionRational& HighPrecisionRational::operator=(const HighPrecisionRational& other) {
    if (this != &other) {
        value = other.value;
    }
    return *this;
}

HighPrecisionRational HighPrecisionRational::operator+(const HighPrecisionRational& other) const {
    return HighPrecisionRational(value + other.value);
}

HighPrecisionRational HighPrecisionRational::operator-(const HighPrecisionRational& other) const {
    return HighPrecisionRational(value - other.value);
}

HighPrecisionRational HighPrecisionRational::operator-() const {
    return HighPrecisionRational(-value);
}

HighPrecisionRational HighPrecisionRational::operator*(const HighPrecisionRational& other) const {
    return HighPrecisionRational(value * other.value);
}

HighPrecisionRational HighPrecisionRational::operator/(const HighPrecisionRational& other) const {
    return HighPrecisionRational(value / other.value);
}

bool HighPrecisionRational::operator==(const HighPrecisionRational& other) const {
    return value == other.value;
}

bool HighPrecisionRational::operator!=(const HighPrecisionRational& other) const {
    return value != other.value;
}

bool HighPrecisionRational::operator<(const HighPrecisionRational& other) const {
    return value < other.value;
}

bool HighPrecisionRational::operator<=(const HighPrecisionRational& other) const {
    return value <= other.value;
}

bool HighPrecisionRational::operator>(const HighPrecisionRational& other) const {
    return value > other.value;
}

bool HighPrecisionRational::operator>=(const HighPrecisionRational& other) const {
    return value >= other.value;
}

std::string HighPrecisionRational::toString() const {
    if (value.get_den() == 1) {
        return value.get_num().get_str();
    }
    return value.get_num().get_str() + "/" + value.get_den().get_str();
}

double HighPrecisionRational::toDouble() const {
    return value.get_d();
}

bool HighPrecisionRational::isInteger() const {
    return value.get_den() == 1;
}

const mpq_class& HighPrecisionRational::getMPQ() const {
    return value;
}

mpq_class& HighPrecisionRational::getMPQ() {
    return value;
}

// HighPrecisionReal constructor from mpq_class
HighPrecisionReal::HighPrecisionReal(const mpq_class& q, mpfr_prec_t precision) {
    mpfr_init2(value, precision);
    mpfr_set_q(value, q.get_mpq_t(), MPFR_RNDN);
}

// -------------Number-------------
// Constructor
Number::Number() : type(INT_TYPE), intValue(0) {}

Number::Number(const HighPrecisionInteger& i) 
    : type(INT_TYPE), intValue(i) {}

Number::Number(const HighPrecisionRational& r) {
    const mpq_class& q = r.getMPQ();
    if (q.get_den() == 1) {
        type = INT_TYPE;
        intValue = HighPrecisionInteger(q.get_num().get_str());
    } else {
        type = RATIONAL_TYPE;
        ratValue = r;
    }
}

Number::Number(const HighPrecisionReal& r) 
    : type(REAL_TYPE), realValue(r) {}

Number::Number(int i) 
    : type(INT_TYPE), intValue(i) {}

Number::Number(double d, bool asInteger) {
    if (asInteger) {
        type = INT_TYPE;
        intValue = HighPrecisionInteger(d);
    } else {
        type = REAL_TYPE;
        realValue = HighPrecisionReal(d);
    }
}

Number::Number(const std::string& s, bool asInteger) {
    // Simple integer check: optional leading +/-, then all digits
    bool isIntString = !s.empty();
    for (size_t i = 0; i < s.size(); ++i) {
        if (i == 0 && (s[i] == '-' || s[i] == '+')) continue;
        if (!isdigit(static_cast<unsigned char>(s[i]))) { isIntString = false; break; }
    }
    if (asInteger || isIntString) {
        type = INT_TYPE;
        intValue = HighPrecisionInteger(s);
    } else {
        HighPrecisionRational rational(s);
        if (rational.isInteger()) {
            type = INT_TYPE;
            intValue = HighPrecisionInteger(
                rational.getMPQ().get_num().get_str());
        } else {
            type = RATIONAL_TYPE;
            ratValue = std::move(rational);
        }
    }
}

Number::Number(const Number& other) : type(other.type) {
    if (type == INT_TYPE) {
        intValue = other.intValue;
    } else if (type == RATIONAL_TYPE) {
        ratValue = other.ratValue;
    } else {
        realValue = other.realValue;
    }
}

// Assignment operator
Number& Number::operator=(const Number& other) {
    if (this != &other) {
        type = other.type;
        if (type == INT_TYPE) {
            intValue = other.intValue;
        } else if (type == RATIONAL_TYPE) {
            ratValue = other.ratValue;
        } else {
            realValue = other.realValue;
        }
    }
    return *this;
}

// Destructor
Number::~Number() {
    // No special handling needed, HighPrecisionInteger and HighPrecisionReal will clean up automatically
}

// Get value
const HighPrecisionInteger& Number::getInteger() const {
    if (type != INT_TYPE) {
        throw std::runtime_error("Number is not an integer");
    }
    return intValue;
}

const HighPrecisionRational& Number::getRational() const {
    if (type != RATIONAL_TYPE) {
        throw std::runtime_error("Number is not a rational");
    }
    return ratValue;
}

const HighPrecisionReal& Number::getReal() const {
    if (type != REAL_TYPE) {
        throw std::runtime_error("Number is not a real");
    }
    return realValue;
}

// Type conversion
std::optional<HighPrecisionInteger> Number::asIntegerExact() const {
    if (type == INT_TYPE) {
        return intValue;
    } else if (type == RATIONAL_TYPE) {
        if (ratValue.getMPQ().get_den() == 1) {
            return HighPrecisionInteger(ratValue.getMPQ().get_num().get_str());
        }
        return std::nullopt;
    } else {
        // REAL_TYPE is approximate; cannot provide exact integer
        return std::nullopt;
    }
}

HighPrecisionInteger Number::floorToInteger() const {
    if (type == INT_TYPE) {
        return intValue;
    } else if (type == RATIONAL_TYPE) {
        mpz_class q;
        mpz_fdiv_q(q.get_mpz_t(), ratValue.getMPQ().get_num().get_mpz_t(), ratValue.getMPQ().get_den().get_mpz_t());
        return HighPrecisionInteger(q.get_str());
    } else {
        return realValue.toInteger();
    }
}

HighPrecisionRational Number::toRationalExact() const {
    if (type == INT_TYPE) {
        return HighPrecisionRational(intValue.getMPZ());
    } else if (type == RATIONAL_TYPE) {
        return ratValue;
    } else {
        throw std::runtime_error("Cannot convert approximate REAL_TYPE to exact rational");
    }
}

HighPrecisionRational Number::approximateToRational() const {
    if (type == INT_TYPE) {
        return HighPrecisionRational(intValue.getMPZ());
    } else if (type == RATIONAL_TYPE) {
        return ratValue;
    } else {
        // REAL_TYPE fallback: parse string representation as rational
        return HighPrecisionRational(realValue.toString());
    }
}

HighPrecisionReal Number::toReal(mpfr_prec_t precision) const {
    if (type == REAL_TYPE) {
        return realValue;
    } else if (type == RATIONAL_TYPE) {
        return HighPrecisionReal(ratValue.getMPQ(), precision);
    } else {
        return HighPrecisionReal(intValue, precision);
    }
}

Number Number::zero() {
    return Number(0);
}
Number Number::one() {
    return Number(1);
}

Number Number::fromApproxDouble(double v) {
    return Number(HighPrecisionReal(v));
}

Number Number::fromExactDecimalString(const std::string& s) {
    return Number(s, false); // Always RATIONAL_TYPE (exact)
}
Number Number::infinity() {
    // 无穷必须用 REAL_TYPE 表示，因为整数无法表示无穷
    // 使用 HighPrecisionReal 构造函数，自动设置 type = REAL_TYPE
    HighPrecisionReal inf(128);
    mpfr_set_inf(inf.getMPFR(), 1);
    return Number(inf);
}
Number Number::negativeInfinity() {
    HighPrecisionReal negInf(128);
    mpfr_set_inf(negInf.getMPFR(), -1);
    return Number(negInf);
}
Number Number::positiveInfinity() {
    HighPrecisionReal posInf(128);
    mpfr_set_inf(posInf.getMPFR(), 1);
    return Number(posInf);
}
bool Number::isZero() const {
    if(type == INT_TYPE) {
        return intValue == 0;
    } else if(type == RATIONAL_TYPE) {
        return ratValue.getMPQ().get_num() == 0;
    }
    return realValue == 0;
}
bool Number::isOne() const {
    if(type == INT_TYPE) {
        return intValue == 1;
    } else if(type == RATIONAL_TYPE) {
        return ratValue.getMPQ().get_num() == 1 && ratValue.getMPQ().get_den() == 1;
    }
    return realValue == 1;
}
bool Number::isInfinity() const {
    if(type == INT_TYPE || type == RATIONAL_TYPE) {
        return false;
    }
    return realValue.isInfinity();
}

bool Number::isNegativeInfinity() const {
    if(type == INT_TYPE || type == RATIONAL_TYPE) {
        return false;
    }
    return realValue.isNegativeInfinity();
}
bool Number::isPositiveInfinity() const {
    if(type == INT_TYPE || type == RATIONAL_TYPE) {
        return false;
    }
    return realValue.isPositiveInfinity();
}
Number Number::pi(size_t precision) {
    return Number(HighPrecisionReal::pi(precision));
}
Number Number::e(size_t precision) {
    return Number(HighPrecisionReal::e(precision));
}
Number Number::phi(size_t precision) {
    return Number(HighPrecisionReal::phi(precision));
}
Number Number::ln2(size_t precision) {
    return Number(HighPrecisionReal::ln2(precision));
}
Number Number::ln10(size_t precision) {
    return Number(HighPrecisionReal::ln10(precision));
}
Number Number::log2_e(size_t precision) {
    return Number(HighPrecisionReal::log2_e(precision));
}
Number Number::log10_e(size_t precision) {
    return Number(HighPrecisionReal::log10_e(precision));
}
Number Number::epsilon(size_t precision) {
    return Number(HighPrecisionReal::epsilon(precision));
}

// Basic operations
Number Number::operator+(const Number& other) const {
    if (type == INT_TYPE && other.type == INT_TYPE) {
        return Number(intValue + other.intValue);
    }
    // If any side is RATIONAL and neither is REAL, stay exact
    if ((type == RATIONAL_TYPE || other.type == RATIONAL_TYPE) &&
        type != REAL_TYPE && other.type != REAL_TYPE) {
        return Number(toRationalExact() + other.toRationalExact());
    }
    return Number(toReal() + other.toReal());
}

Number Number::operator-(const Number& other) const {
    if (type == INT_TYPE && other.type == INT_TYPE) {
        return Number(intValue - other.intValue);
    }
    if ((type == RATIONAL_TYPE || other.type == RATIONAL_TYPE) &&
        type != REAL_TYPE && other.type != REAL_TYPE) {
        return Number(toRationalExact() - other.toRationalExact());
    }
    return Number(toReal() - other.toReal());
}

Number Number::operator-() const {
    if (type == INT_TYPE) {
        return Number(-intValue);
    } else if (type == RATIONAL_TYPE) {
        return Number(-ratValue);
    }
    return Number(-realValue);
}

Number Number::operator*(const Number& other) const {
    if (type == INT_TYPE && other.type == INT_TYPE) {
        return Number(intValue * other.intValue);
    }
    if ((type == RATIONAL_TYPE || other.type == RATIONAL_TYPE) &&
        type != REAL_TYPE && other.type != REAL_TYPE) {
        return Number(toRationalExact() * other.toRationalExact());
    }
    return Number(toReal() * other.toReal());
}

Number Number::operator/(const Number& other) const {
    if (type == INT_TYPE && other.type == INT_TYPE) {
        if (intValue % other.intValue == HighPrecisionInteger(0)) {
            return Number(intValue / other.intValue);
        }
        // Non-divisible integer division -> exact rational
        return Number(HighPrecisionRational(intValue.getMPZ()) / HighPrecisionRational(other.intValue.getMPZ()));
    }
    if ((type == RATIONAL_TYPE || other.type == RATIONAL_TYPE) &&
        type != REAL_TYPE && other.type != REAL_TYPE) {
        return Number(toRationalExact() / other.toRationalExact());
    }
    return Number(toReal() / other.toReal());
}

Number Number::operator%(const Number& other) const {
    condAssert(type == INT_TYPE && other.type == INT_TYPE, "Cannot compute modulo of non-integer numbers");
    return Number(intValue % other.intValue);
}

Number& Number::operator+=(const Number& other) {
    if (type == INT_TYPE && other.type == INT_TYPE) {
        intValue += other.intValue;
    } else if (type == RATIONAL_TYPE && other.type == RATIONAL_TYPE) {
        ratValue = ratValue + other.ratValue;
    } else if (type == RATIONAL_TYPE && other.type == INT_TYPE) {
        ratValue = ratValue + HighPrecisionRational(other.intValue.getMPZ());
    } else if (type == INT_TYPE && other.type == RATIONAL_TYPE) {
        type = RATIONAL_TYPE;
        ratValue = HighPrecisionRational(intValue.getMPZ()) + other.ratValue;
    } else {
        realValue += other.toReal();
    }
    return *this;
}

Number& Number::operator-=(const Number& other) {
    if (type == INT_TYPE && other.type == INT_TYPE) {
        intValue -= other.intValue;
    } else if (type == RATIONAL_TYPE && other.type == RATIONAL_TYPE) {
        ratValue = ratValue - other.ratValue;
    } else if (type == RATIONAL_TYPE && other.type == INT_TYPE) {
        ratValue = ratValue - HighPrecisionRational(other.intValue.getMPZ());
    } else if (type == INT_TYPE && other.type == RATIONAL_TYPE) {
        type = RATIONAL_TYPE;
        ratValue = HighPrecisionRational(intValue.getMPZ()) - other.ratValue;
    } else {
        realValue -= other.toReal();
    }
    return *this;
}

Number& Number::operator*=(const Number& other) {
    if (type == INT_TYPE && other.type == INT_TYPE) {
        intValue *= other.intValue;
    } else if (type == RATIONAL_TYPE && other.type == RATIONAL_TYPE) {
        ratValue = ratValue * other.ratValue;
    } else if (type == RATIONAL_TYPE && other.type == INT_TYPE) {
        ratValue = ratValue * HighPrecisionRational(other.intValue.getMPZ());
    } else if (type == INT_TYPE && other.type == RATIONAL_TYPE) {
        type = RATIONAL_TYPE;
        ratValue = HighPrecisionRational(intValue.getMPZ()) * other.ratValue;
    } else {
        realValue *= other.toReal();
    }
    return *this;
}

Number& Number::operator/=(const Number& other) {
    if (type == INT_TYPE && other.type == INT_TYPE) {
        intValue /= other.intValue;
    } else if (type == RATIONAL_TYPE && other.type == RATIONAL_TYPE) {
        ratValue = ratValue / other.ratValue;
    } else if (type == RATIONAL_TYPE && other.type == INT_TYPE) {
        ratValue = ratValue / HighPrecisionRational(other.intValue.getMPZ());
    } else if (type == INT_TYPE && other.type == RATIONAL_TYPE) {
        type = RATIONAL_TYPE;
        ratValue = HighPrecisionRational(intValue.getMPZ()) / other.ratValue;
    } else {
        realValue /= other.toReal();
    }
    return *this;
}

Number& Number::operator%=(const Number& other) {
    condAssert(type == INT_TYPE && other.type == INT_TYPE, "Cannot compute modulo of non-integer numbers");
    intValue %= other.intValue;
    return *this;
}


Number& Number::operator++() {
    if (type == INT_TYPE) {
        intValue++;
    } else if (type == RATIONAL_TYPE) {
        ratValue = ratValue + HighPrecisionRational(1);
    } else {
        realValue = realValue + 1;
    }
    return *this;
}
Number Number::operator++(int) {
    Number temp = *this;
    operator++();
    return temp;
}
Number& Number::operator--() {
    if (type == INT_TYPE) {
        intValue--;
    } else if (type == RATIONAL_TYPE) {
        ratValue = ratValue - HighPrecisionRational(1);
    } else {
        realValue = realValue - 1;
    }
    return *this;
}
Number Number::operator--(int) {
    Number temp = *this;
    operator--();
    return temp;
}

// Bitwise operators
Number Number::operator&(const Number& other) const {
    condAssert(type == INT_TYPE && other.type == INT_TYPE, "Bitwise AND requires integer operands");
    return Number(intValue & other.intValue);
}

Number Number::operator|(const Number& other) const {
    condAssert(type == INT_TYPE && other.type == INT_TYPE, "Bitwise OR requires integer operands");
    return Number(intValue | other.intValue);
}

Number Number::operator^(const Number& other) const {
    condAssert(type == INT_TYPE && other.type == INT_TYPE, "Bitwise XOR requires integer operands");
    return Number(intValue ^ other.intValue);
}

Number Number::operator~() const {
    condAssert(type == INT_TYPE, "Bitwise NOT requires integer operand");
    return Number(~intValue);
}

Number Number::operator<<(unsigned long bits) const {
    condAssert(type == INT_TYPE, "Left shift requires integer operand");
    return Number(intValue << bits);
}

Number Number::operator>>(unsigned long bits) const {
    condAssert(type == INT_TYPE, "Right shift requires integer operand");
    return Number(intValue >> bits);
}

// Comparison operators
bool Number::operator==(const Number& other) const {
    if (type == other.type) {
        if (type == INT_TYPE) {
            return intValue == other.intValue;
        } else if (type == RATIONAL_TYPE) {
            return ratValue == other.ratValue;
        } else {
            return realValue == other.realValue;
        }
    }
    // When types are different
    if (type == REAL_TYPE || other.type == REAL_TYPE) {
        return toReal() == other.toReal();
    }
    // INT vs RATIONAL: compare via rational
    return toRationalExact() == other.toRationalExact();
}

bool Number::operator!=(const Number& other) const {
    return !(*this == other);
}

bool Number::operator<(const Number& other) const {
    if (type == other.type) {
        if (type == INT_TYPE) {
            return intValue < other.intValue;
        } else if (type == RATIONAL_TYPE) {
            return ratValue < other.ratValue;
        } else {
            return realValue < other.realValue;
        }
    }
    if (type == REAL_TYPE || other.type == REAL_TYPE) {
        return toReal() < other.toReal();
    }
    return toRationalExact() < other.toRationalExact();
}

bool Number::operator<=(const Number& other) const {
    if (type == other.type) {
        if (type == INT_TYPE) {
            return intValue <= other.intValue;
        } else if (type == RATIONAL_TYPE) {
            return ratValue <= other.ratValue;
        } else {
            return realValue <= other.realValue;
        }
    }
    if (type == REAL_TYPE || other.type == REAL_TYPE) {
        return toReal() <= other.toReal();
    }
    return toRationalExact() <= other.toRationalExact();
}

bool Number::operator>(const Number& other) const {
    return !(*this <= other);
}

bool Number::operator>=(const Number& other) const {
    return !(*this < other);
}

// Convert to string
std::string Number::toString() const {
    if (type == INT_TYPE) {
        return intValue.toString();
    } else if (type == RATIONAL_TYPE) {
        return ratValue.toString();
    } else {
        return realValue.toString();
    }
}

// Mathematical functions
Number Number::abs() const {
    if (type == INT_TYPE) {
        return Number(intValue.abs());
    } else if (type == RATIONAL_TYPE) {
        mpq_class absVal = ratValue.getMPQ();
        mpz_abs(absVal.get_num_mpz_t(), absVal.get_num_mpz_t());
        return Number(HighPrecisionRational(absVal));
    } else {
        return Number(realValue.abs());
    }
}

Number Number::sqrt() const {
    if (type == INT_TYPE) {
        HighPrecisionInteger root = intValue.sqrt();
        return Number(root);
    }
    return Number(toReal().sqrt());
}

Number Number::safeSqrt() const {
    if (type == INT_TYPE) {
        HighPrecisionInteger root = intValue.safeSqrt();
        return Number(root);
    }
    return Number(toReal().safeSqrt());
}

Number Number::pow(const Number& exp) const {
    if (type == INT_TYPE && exp.type == INT_TYPE) {
        if (exp.intValue >= HighPrecisionInteger(0)) {
            try {
                unsigned long expVal = exp.intValue.toULong();
                return Number(intValue.pow(expVal));
            } catch (const std::overflow_error&) {
                // fall through
            }
        }
    }
    return Number(toReal().pow(exp.toReal()));
}

// Rounding operations
Number Number::ceil() const {
    if (type == INT_TYPE) {
        return Number(intValue);
    } else if (type == RATIONAL_TYPE) {
        mpz_class q;
        mpz_cdiv_q(q.get_mpz_t(), ratValue.getMPQ().get_num().get_mpz_t(), ratValue.getMPQ().get_den().get_mpz_t());
        return Number(HighPrecisionInteger(q.get_str()));
    } else {
        return Number(realValue.ceil());
    }
}

Number Number::floor() const {
    if (type == INT_TYPE) {
        return Number(intValue);
    } else if (type == RATIONAL_TYPE) {
        mpz_class q;
        mpz_fdiv_q(q.get_mpz_t(), ratValue.getMPQ().get_num().get_mpz_t(), ratValue.getMPQ().get_den().get_mpz_t());
        return Number(HighPrecisionInteger(q.get_str()));
    } else {
        return Number(realValue.floor());
    }
}

Number Number::round() const {
    if (type == INT_TYPE) {
        return Number(intValue);
    } else if (type == RATIONAL_TYPE) {
        mpz_class q;
        mpz_t r;
        mpz_init(r);
        mpz_fdiv_qr(q.get_mpz_t(), r, ratValue.getMPQ().get_num().get_mpz_t(), ratValue.getMPQ().get_den().get_mpz_t());
        mpz_class den2 = ratValue.getMPQ().get_den();
        mpz_mul_ui(den2.get_mpz_t(), den2.get_mpz_t(), 2);
        if (mpz_cmpabs(r, den2.get_mpz_t()) >= 0) {
            // remainder >= den/2, round away from zero
            if (mpz_sgn(ratValue.getMPQ().get_num().get_mpz_t()) >= 0)
                mpz_add_ui(q.get_mpz_t(), q.get_mpz_t(), 1);
            else
                mpz_sub_ui(q.get_mpz_t(), q.get_mpz_t(), 1);
        }
        mpz_clear(r);
        return Number(HighPrecisionInteger(q.get_str()));
    } else {
        return Number(realValue.round());
    }
}

// Exponential and logarithmic functions
Number Number::exp() const{
    return Number(toReal().exp());
}
Number Number::ln() const{
    return Number(toReal().ln());
}
Number Number::lg() const{
    return Number(toReal().lg());
}
Number Number::lb() const{
    return Number(toReal().lb());
}
Number Number::log(const Number& base) const{
    return Number(toReal().log(base.toReal()));
}

// Trigonometric functions
Number Number::sin() const{
    return Number(toReal().sin());
}
Number Number::cos() const{
    return Number(toReal().cos());
}
Number Number::tan() const{
    return Number(toReal().tan());
}
Number Number::cot() const{
    return Number(toReal().cot());
}
Number Number::sec() const{
    return Number(toReal().sec());
}
Number Number::csc() const{
    return Number(toReal().csc());
}
Number Number::asin() const{
    return Number(toReal().asin());
}
Number Number::acos() const{
    return Number(toReal().acos());
}
Number Number::atan() const{
    return Number(toReal().atan());
}
Number Number::acot() const{
    return Number(toReal().acot());
}
Number Number::asec() const{
    return Number(toReal().asec());
}
Number Number::acsc() const{
    return Number(toReal().acsc());
}
Number Number::atan2(const Number& y, const Number& x){
    return Number(HighPrecisionReal::atan2(y.toReal(), x.toReal()));
}

// Hyperbolic functions
Number Number::sinh() const{
    return Number(toReal().sinh());
}
Number Number::cosh() const{
    return Number(toReal().cosh());
}
Number Number::tanh() const{
    return Number(toReal().tanh());
}
Number Number::coth() const{
    return Number(toReal().coth());
}
Number Number::sech() const{
    return Number(toReal().sech());
}
Number Number::csch() const{
    return Number(toReal().csch());
}
Number Number::asinh() const{
    return Number(toReal().asinh());
}
Number Number::acosh() const{
    return Number(toReal().acosh());
}
Number Number::atanh() const{
    return Number(toReal().atanh());
}
Number Number::asech() const{
    return Number(toReal().asech());
}
Number Number::acsch() const{
    return Number(toReal().acsch());
}
Number Number::acoth() const{
    return Number(toReal().acoth());
}
Number Number::nextBelow() const {
    if (type == INT_TYPE) {
        return Number(intValue.nextBelow());
    } else if (type == RATIONAL_TYPE) {
        return Number(toReal().nextBelow());
    } else {
        return Number(realValue.nextBelow());
    }
}

Number Number::nextAbove() const {
    if (type == INT_TYPE) {
        return Number(intValue.nextAbove());
    } else if (type == RATIONAL_TYPE) {
        return Number(toReal().nextAbove());
    } else {
        return Number(realValue.nextAbove());
    }
}

bool Number::isNaN() const {
    if (type == INT_TYPE || type == RATIONAL_TYPE) {
        return false;
    }
    return realValue.isNaN();
}

} // namespace SOMTParser
