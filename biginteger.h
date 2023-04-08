#include <cstddef>
#include <cstdio>
#include <cstdlib>
#include <initializer_list>
#include <iostream>
#include <algorithm>
#include <stdexcept>
#include <vector>
#include <limits>
#include <compare>
#include <iterator>
#include <string_view>
#include <cmath>
#include <sstream>
#include <iomanip>
#include <complex>
#include <numbers>
#include <array>
#include <cassert>


constexpr unsigned long long integralPow(unsigned long long val, size_t exp) {
    unsigned long long result = 1;
    while(exp--) {
        result *= val;
    }
    return result;
}

class BigInteger {
private:
    using DigitT = int32_t;
    using DigitSequence = std::vector<DigitT>;

    static const int    base_exp       = 10;
    static const int    base_exp_power = 4;
    static const DigitT base           = integralPow(base_exp, base_exp_power); 

    DigitSequence digits_; // invariant: leading digit isn't zero

    enum class SignT {
        NEGATIVE = -1,
        ZERO = 0,
        POSITIVE = 1,
    };

    SignT sign_ = SignT::ZERO;

private: // sign section
    void flipSign() {
        sign_ = static_cast<SignT>(-1 * static_cast<int>(sign_));
    }
    
    static bool oppositeSigns(SignT sign1, SignT sign2) {
        return static_cast<int>(sign1) * static_cast<int>(sign2) == -1;
    }

    static SignT addSigns(SignT sign1, SignT sign2) {
        return sign1 == sign2
            ? sign1 
            : static_cast<SignT>(static_cast<int>(sign1) + static_cast<int>(sign2));
    }

    static SignT mulSigns(SignT sign1, SignT sign2) {
        return static_cast<SignT>(static_cast<int>(sign1) * static_cast<int>(sign2));
    }
    
    void checkAndProcessDigitsEmptiness() {
        if (digits_.empty()) {
            sign_ = SignT::ZERO;
        }
    }

// fft section
    static size_t reverseBits(size_t x, size_t modulo) {
        size_t x_reversed = 0;
        for (size_t bit_i = 0; (modulo >> bit_i) != 1; ++bit_i) {
            x_reversed = (x_reversed << 1) | ((x >> bit_i) & 1);
        }
        return x_reversed;
    }
    
    static void fft(std::vector<std::complex<long double>>& a, std::complex<long double> w0) {
        size_t n = a.size();
        
        for (size_t i = 0; i < n; ++i) {
            size_t i_rev = reverseBits(i, n);
            assert(i_rev < n);
            if (i < i_rev) {
                std::swap(a[i], a[i_rev]);
            }
        }

        for (size_t level = 1; (n >> level) != 0; ++level) {
            std::complex<long double> w_step = w0;
            for (size_t i = 1; (n >> level >> i) != 0; ++i) {
                w_step *= w_step;
            }

            size_t chunk_sz = (1ull << level);
            for (size_t chunk_start = 0; chunk_start < n; chunk_start += chunk_sz) {
                std::complex<long double> w = 1;
                for (size_t offset = 0; offset < (chunk_sz >> 1); ++offset) {
                    size_t i           = chunk_start + offset;
                    size_t conjugate_i = i + (chunk_sz >> 1);
                    std::complex<long double> x = a[i          ];
                    std::complex<long double> y = a[conjugate_i];
                    a[i          ] = x + w * y;
                    a[conjugate_i] = x - w * y;
                    w *= w_step;
                }
            }
        }
    }

    static void mulPolynoms(std::vector<long double>& lhs, const std::vector<long double>& rhs) {
        size_t n = 1;
        while (n < std::max(lhs.size(), rhs.size())) {
            n <<= 1;
        }
        n <<= 1;
        std::vector<std::complex<long double>> a(n, 0), b(n, 0);
        
        std::copy(lhs.begin(), lhs.end(), a.begin());
        std::copy(rhs.begin(), rhs.end(), b.begin());
        
        long double arg = 2 * std::numbers::pi_v<long double> / static_cast<long double>(n);
        std::complex<long double> w0(std::cos(arg), std::sin(arg));
        
        fft(a, w0);
        fft(b, w0);
        for (size_t i = 0; i < n; ++i) {
            a[i] *= b[i];
        }

        fft(a, std::conj(w0));
        lhs.resize(n);
        for (size_t i = 0; i < n; ++i) {
            lhs[i] = a[i].real() / n;
        }
    }

// digit section
    static std::strong_ordering compareDigits(
            const DigitSequence& lhs, const DigitSequence& rhs) {
       if (lhs.size() != rhs.size()) return lhs.size() <=> rhs.size();
       for (size_t digit_i = lhs.size(); digit_i >= 1; --digit_i) {
           const DigitT& l_digit = lhs[digit_i - 1];
           const DigitT& r_digit = rhs[digit_i - 1];
           if (l_digit != r_digit) {
               return l_digit <=> r_digit;
           }
       }
       return std::strong_ordering::equal;
    }

    static void deleteLeadingZeros(DigitSequence& digits) {
        while (!digits.empty() && digits.back() == 0) {
            digits.pop_back();
        }
    }

    static DigitT getDigit(const DigitSequence& digits, size_t i) {
        return i >= digits.size() ? 0 : digits[i];
    }

    enum class AlgebraicSumSignT {
        MINUS = -1,
        PLUS  = +1,
    };

    template<AlgebraicSumSignT Sign>
    static void addDigitsAlgebraically(
            DigitSequence& lhs, const DigitSequence& rhs, bool inverse_addition = false) {
        bool transfer = false;
        for (size_t digit_i = 0; digit_i < std::max(lhs.size(), rhs.size()); ++digit_i) {
            if (digit_i >= lhs.size()) lhs.push_back(0);
            if (digit_i >= rhs.size() && !transfer) break;

            DigitT& l_digit = lhs[digit_i];
            DigitT  r_digit = getDigit(rhs, digit_i);
            if (inverse_addition) {
                std::swap(l_digit, r_digit);
            }
            
            if constexpr (Sign == AlgebraicSumSignT::PLUS) {
                l_digit  += transfer + r_digit; 
                transfer  = l_digit >= base;
                l_digit  %= base;
            } else {
                l_digit  -= r_digit + transfer;
                transfer  = l_digit < 0;
                l_digit   = (l_digit + base) % base;
            }
        }

        if constexpr (Sign == AlgebraicSumSignT::PLUS) {
            if (transfer) { 
                lhs.push_back(1);
            }
        } else {
            deleteLeadingZeros(lhs);
        }
    }

    static void multiplyDigitsPowerBaseExp(DigitSequence& digits, size_t power) {
        if (digits.empty()) return;
        digits.insert(digits.begin(), power / base_exp_power, 0);
        power %= base_exp_power;
        unsigned long long factor = integralPow(base_exp, power);
        unsigned long long transfer = 0;
        for (size_t digit_i = 0; digit_i < digits.size(); ++digit_i) {
            transfer += factor * static_cast<unsigned long long>(digits[digit_i]);
            digits[digit_i] = static_cast<DigitT>(transfer % base);
            transfer /= base;
        }
        if (transfer != 0) {
            digits.push_back(static_cast<DigitT>(transfer));
        }
    }

    static void divideDigitsPowerBaseExp(DigitSequence& digits, size_t power) {
        size_t n_digits_to_delete = std::min(power / base_exp_power, digits.size());
        digits.erase(digits.begin(), digits.begin() + static_cast<long long>(n_digits_to_delete));
        power %= base_exp_power;
        unsigned long long divider = integralPow(base_exp, power);
        for (size_t digit_i = 0; digit_i < digits.size(); ++digit_i) {
            if (digit_i != 0) {
                digits[digit_i - 1] += static_cast<DigitT>((static_cast<unsigned long long>(digits[digit_i]) % divider) * (base / divider)); 
            }
            digits[digit_i] /= static_cast<DigitT>(divider);
        }
        deleteLeadingZeros(digits);
    }

    static void divDigits(DigitSequence& lhs, DigitSequence rhs, bool modulo) {
        size_t result_power_base_exp = base_exp_power * (lhs.size() - std::min(lhs.size(), rhs.size()) + 1);
        multiplyDigitsPowerBaseExp(rhs, result_power_base_exp);
        DigitSequence result;
        while (result_power_base_exp--) {
            divideDigitsPowerBaseExp(rhs, 1);
            multiplyDigitsPowerBaseExp(result, 1);
            while (compareDigits(lhs, rhs) >= 0) {
                if (result.empty()) {
                    result.push_back(0);
                }
                ++result.front();
                addDigitsAlgebraically<AlgebraicSumSignT::MINUS>(lhs, rhs);
            }
        }
        deleteLeadingZeros(result);
        if (!modulo) {
            std::swap(lhs, result);
        }
    }

    static void mulDigits(DigitSequence& lhs, const DigitSequence& rhs) {
        std::vector<long double> l_poly(lhs.begin(), lhs.end());
        std::vector<long double> r_poly(rhs.begin(), rhs.end());

        mulPolynoms(l_poly, r_poly);
        unsigned long long transfer = 0;
        for (size_t i = 0; i < l_poly.size(); ++i) {
            if (i >= lhs.size()) lhs.push_back(0);
            transfer += static_cast<unsigned long long>(std::round(l_poly[i]));
            lhs[i] = static_cast<DigitT>(transfer % base);
            transfer /= base;
        }
        while (transfer != 0) {
            lhs.push_back(static_cast<DigitT>(transfer % base));
            transfer /= base;
        }
        deleteLeadingZeros(lhs);
    }

public:
    BigInteger(): sign_(SignT::ZERO) {}

    BigInteger(long long x)
    : sign_(x == 0 ? SignT::ZERO     :
            x <  0 ? SignT::NEGATIVE :
                     SignT::POSITIVE ) 
    {
        x = std::abs(x);
        while (x != 0) {
            digits_.push_back(static_cast<DigitT>(x % base));
            x /= base;
        }
    }

    BigInteger(std::string_view str) {
        while (!str.empty() && str.front() == '0') {
            str.remove_prefix(1);
        }
        if (str.empty()){
            sign_ = SignT::ZERO;
            return;
        }
        sign_ = SignT::POSITIVE;
        if (str.front() == '-') {
            sign_ = SignT::NEGATIVE;
            str.remove_prefix(1);
        }
        //
        while (!str.empty()) {
            size_t chunk_size = std::min(static_cast<size_t>(base_exp_power), str.size());
            std::string_view digit_token = str.substr(str.size() - chunk_size, chunk_size);
            str.remove_suffix(chunk_size);
            digits_.push_back(static_cast<DigitT>(std::stoll(std::string(digit_token))));
        }
    }
    
    std::strong_ordering operator<=>(const BigInteger& rhs) const {
        if (sign_ != rhs.sign_) {
            return sign_ <=> rhs.sign_;
        }
        return sign_ == SignT::POSITIVE 
            ? compareDigits(digits_    , rhs.digits_) 
            : compareDigits(rhs.digits_, digits_);
    }

    bool operator==(const BigInteger& rhs) const = default;

    BigInteger& operator+=(const BigInteger& rhs) {
        if (oppositeSigns(sign_, rhs.sign_)) {
            flipSign();
            operator-=(rhs);
            flipSign();
            return *this;
        }
        addDigitsAlgebraically<AlgebraicSumSignT::PLUS>(digits_, rhs.digits_);
        sign_ = addSigns(sign_, rhs.sign_);
        return *this;
    }

    BigInteger& operator-=(const BigInteger& rhs) {
        if (oppositeSigns(sign_, rhs.sign_)) {
            flipSign();
            operator+=(rhs);
            flipSign();
            return *this;
        }
        sign_ = addSigns(sign_, rhs.sign_);
        bool inverse_subtraction = compareDigits(digits_, rhs.digits_) < 0;
        addDigitsAlgebraically<AlgebraicSumSignT::MINUS>(digits_, rhs.digits_, inverse_subtraction);
        checkAndProcessDigitsEmptiness();
        if (inverse_subtraction) flipSign();
        return *this;
    }
    
    BigInteger& operator *=(const BigInteger& rhs) {
        sign_ = mulSigns(sign_, rhs.sign_);
        mulDigits(digits_, rhs.digits_);
        return *this; 
    }

    BigInteger& operator /=(const BigInteger& rhs) {
        sign_ = mulSigns(sign_, rhs.sign_);
        divDigits(digits_, rhs.digits_, false);
        checkAndProcessDigitsEmptiness();
        return *this; 
    }

    BigInteger& operator %=(const BigInteger& rhs) {
        divDigits(digits_, rhs.digits_, true);
        checkAndProcessDigitsEmptiness();
        return *this;
    }

    std::string toString() const {
        std::ostringstream result;
        result << (sign_ == SignT::ZERO     ? "0" :  
                   sign_ == SignT::NEGATIVE ? "-" :
                                              ""  );
        for (size_t i = digits_.size(); i >= 1; --i) {
            if (i != digits_.size()) {
                result << std::setfill('0') << std::setw(base_exp_power);
            }
            result << digits_[i - 1];

        }
        return result.str();
    }

    BigInteger operator-() const {
        BigInteger result = *this;
        result.flipSign();
        return result;
    }

    BigInteger& operator++() {
        return *this += 1;
    }

    BigInteger operator++(int) {
        BigInteger result = *this;
        *this += 1;
        return result;
    }

    BigInteger& operator--() {
        return *this -= 1;
    }

    BigInteger operator--(int) {
        BigInteger result = *this;
        *this -= 1;
        return result;
    }

    explicit operator bool() const {
        return sign_ != SignT::ZERO; 
    }

    BigInteger& multiplyPowerBaseExp(size_t power) {
        multiplyDigitsPowerBaseExp(digits_, power);
        return *this;
    }

};

BigInteger operator+(const BigInteger& lhs, const BigInteger& rhs) {
    BigInteger result = lhs;
    return result += rhs;
}

BigInteger operator-(const BigInteger& lhs, const BigInteger& rhs) {
    BigInteger result = lhs;
    return result -= rhs;
}

BigInteger operator*(const BigInteger& lhs, const BigInteger& rhs) {
    BigInteger result = lhs;
    return result *= rhs;
}

BigInteger operator/(const BigInteger& lhs, const BigInteger& rhs) {
    BigInteger result = lhs;
    return result /= rhs;
}

BigInteger operator%(const BigInteger& lhs, const BigInteger& rhs) {
    BigInteger result = lhs;
    return result %= rhs;
}

std::ostream& operator<<(std::ostream& output, const BigInteger& bi) {
    return output << bi.toString();
}

std::istream& operator>>(std::istream& input, BigInteger& bi) {
    std::string str;
    input >> str;
    bi = BigInteger(str);
    return input;
}

BigInteger operator"" _bi(unsigned long long x) {
    return BigInteger(static_cast<long long>(x));
}

BigInteger operator"" _bi(const char* str, std::size_t) {
    return BigInteger(str);
}

BigInteger abs(BigInteger x) {
    return x < 0 ? -x : x;
}

BigInteger gcd(BigInteger x, BigInteger y) {
    if (y == 0) {
        return x;
    }
    return gcd(y, x % y);
}

class Rational {
private:
    BigInteger numerator_ = 0, denominator_ = 1; // invariant: denominator > 0
    
    void normalizeFraction() {
        if (denominator_ < 0) {
            numerator_   = -numerator_;
            denominator_ = -denominator_;
        }
        BigInteger common_divisor = gcd(abs(numerator_), denominator_);
        numerator_   /= common_divisor;
        denominator_ /= common_divisor;
    }

public:
    Rational() {}
    Rational(const BigInteger& numerator, const BigInteger& denominator)
        : numerator_(numerator), denominator_(denominator) {
            normalizeFraction();
        }

    Rational(const BigInteger& x): Rational(x, 1) {}
    Rational(int x): Rational(x, 1) {};

    Rational& operator+=(const Rational& that) {
        numerator_   *= that.denominator_;
        numerator_   += that.numerator_ * denominator_;
        denominator_ *= that.denominator_;
        normalizeFraction();
        return *this;
    }

    Rational& operator-=(const Rational& that) {
        numerator_   *= that.denominator_;
        numerator_   -= that.numerator_ * denominator_;
        denominator_ *= that.denominator_;
        normalizeFraction();
        return *this;
    }

    Rational& operator*=(const Rational& that) {
        numerator_   *= that.numerator_;
        denominator_ *= that.denominator_;
        normalizeFraction();
        return *this;
    }
    
    Rational& operator/=(const Rational& that) {
        numerator_   *= that.denominator_;
        denominator_ *= that.numerator_;
        normalizeFraction();
        return *this;
    }

    Rational operator-() const {
        return Rational(-numerator_, denominator_);
    }

    std::strong_ordering operator<=>(const Rational& that) const {
        return numerator_ * that.denominator_ <=> that.numerator_ * denominator_;
    }

    bool operator==(const Rational& that) const = default;

    std::string toString() const {
        std::string result = numerator_.toString();
        if (denominator_ != 1) {
            result += '/' + denominator_.toString();
        }
        return result;
    }

    std::string asDecimal(size_t precision = 0) const {
        BigInteger value = abs(numerator_);
        value.multiplyPowerBaseExp(precision);
        value /= denominator_;
        std::string result = value.toString();
        if (result.size() < precision + 1) {
            result.insert(0, precision + 1 - result.size(), '0');
        }
        result.insert(result.end() - static_cast<long long>(precision), '.');
        if (numerator_ < 0) {
            result.insert(0, "-");
        }
        return result; 
    }
    
    explicit operator double() const {
        static const int precision = std::numeric_limits<double>::digits * 10;
        return std::stod(asDecimal(precision));
    }
};


Rational operator+(const Rational& lhs, const Rational& rhs) {
    Rational result = lhs;
    return result += rhs;
}

Rational operator-(const Rational& lhs, const Rational& rhs) {
    Rational result = lhs;
    return result -= rhs;
}

Rational operator*(const Rational& lhs, const Rational& rhs) {
    Rational result = lhs;
    return result *= rhs;
}

Rational operator/(const Rational& lhs, const Rational& rhs) {
    Rational result = lhs;
    return result /= rhs;
}

std::ostream& operator<<(std::ostream& output, const Rational& rational) {
    return output << rational.toString();
}

