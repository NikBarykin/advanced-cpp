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
#include <functional>


constexpr int intPow(int val, size_t exp) {
    int result = 1;
    while(exp--) {
        result *= val;
    }
    return result;
}

class BigInteger {
private:
    using DigitT = int32_t;
    using DigitSequence = std::vector<DigitT>;


    static const int    base_exp = 10;
    static const int    base_exp_power    = 4;
    static const DigitT base        = intPow(base_exp, base_exp_power);

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

    void fft(std::vector<std::complex<long double>>& a, std::complex<long double> w0) {
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

    void mulPolynoms(std::vector<long double>& lhs, const std::vector<long double>& rhs) {
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
       // for (size_t digit_i = lhs.size(); digit_i-- > 0; ) {
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

    void addDigits(DigitSequence& lhs, DigitSequence rhs) {
        bool transfer = false;
        for (size_t digit_i = 0; digit_i < std::max(lhs.size(), rhs.size()); ++digit_i) {
            if (digit_i >= lhs.size()) lhs.push_back(0);
            if (digit_i >= rhs.size() && !transfer) break;

            DigitT& l_digit = lhs[digit_i];
            l_digit  += transfer + getDigit(rhs, digit_i);
            transfer = l_digit >= base;
            l_digit %= base;
        }
        if (transfer) lhs.push_back(1);
    }

    static void substractDigits(DigitSequence& lhs, DigitSequence rhs,
            bool inverse_substraction = false) {
        bool digit_debt = false;
        for (size_t digit_i = 0; digit_i < std::max(lhs.size(), rhs.size()); ++digit_i) {
            if (digit_i >= lhs.size()) lhs.push_back(0);
            if (digit_i >= rhs.size() && !digit_debt) break;

            DigitT& l_digit = lhs[digit_i];
            DigitT  r_digit = getDigit(rhs, digit_i);
            if (inverse_substraction) std::swap(l_digit, r_digit);
            l_digit -= r_digit + digit_debt;
            digit_debt = l_digit < 0;
            l_digit = (l_digit + base) % base;
        }
        deleteLeadingZeros(lhs);
    }

    static void multiplyDigitsPowerBaseExp(DigitSequence& digits, size_t power) {
        if (digits.empty()) return;
        digits.insert(digits.begin(), power / base_exp_power, 0);
        power %= base_exp_power;
        unsigned long long factor = static_cast<unsigned long long>(intPow(base_exp, power));
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
        unsigned long long divider = static_cast<unsigned long long>(intPow(base_exp, power));
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
                substractDigits(lhs, rhs);
            }
        }
        deleteLeadingZeros(result);
        if (!modulo) {
            std::swap(lhs, result);
        }
    }

    void mulDigits(DigitSequence& lhs, const DigitSequence& rhs) {
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
        if (str.empty()) {
            sign_ = SignT::ZERO;
        } else if (str.front() == '-') {
            sign_ = SignT::NEGATIVE;
            str.remove_prefix(1);
        } else {
            sign_ = SignT::POSITIVE;
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
        addDigits(digits_, rhs.digits_);
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
        bool inverse_substraction = compareDigits(digits_, rhs.digits_) < 0;
        substractDigits(digits_, rhs.digits_, inverse_substraction);
        checkAndProcessDigitsEmptiness();
        if (inverse_substraction) flipSign();
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


BigInteger operator+(BigInteger lhs, const BigInteger& rhs) {
    return lhs += rhs;
}

BigInteger operator-(BigInteger lhs, const BigInteger& rhs) {
    return lhs -= rhs;
}

BigInteger operator*(BigInteger lhs, const BigInteger& rhs) {
    return lhs *= rhs;
}

BigInteger operator/(BigInteger lhs, const BigInteger& rhs) {
    return lhs /= rhs;
}

BigInteger operator%(BigInteger lhs, const BigInteger& rhs) {
    return lhs %= rhs;
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

    Rational(BigInteger x): Rational(x, 1) {}
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
        //while (result.back() == '0') {
        //    result.pop_back();
        //}
        //if (result.back() == '.') {
        //    result.pop_back();
        //}
        if (numerator_ < 0) {
            result.insert(0, "-");
        }
        //if (result.empty() || result.front() == '.') {
        //    result.insert(result.begin(), '0');
        //}
        return result;
    }

    explicit operator double() const {
        static const int precision = std::numeric_limits<double>::digits * 10;
        return std::stod(asDecimal(precision));
    }
};


Rational operator+(Rational lhs, const Rational& rhs) {
    return lhs += rhs;
}

Rational operator-(Rational lhs, const Rational& rhs) {
    return lhs -= rhs;
}

Rational operator*(Rational lhs, const Rational& rhs) {
    return lhs *= rhs;
}

Rational operator/(Rational lhs, const Rational& rhs) {
    return lhs /= rhs;
}


std::ostream& operator<<(std::ostream& output, const Rational& rational) {
    return output << rational.toString();
}

std::istream& operator>>(std::istream& input, Rational& rational) {
    int x = 0;
    input >> x;
    rational = x;
    return input;
}

namespace {
    template<size_t N, size_t potential_divider, bool done>
    struct IsPrimeHelper {
        static const size_t next_potential_divider        = potential_divider + 1;
        static const size_t next_potential_divider_square = next_potential_divider * next_potential_divider;
        static const bool   next_done                     = (next_potential_divider_square > next_potential_divider)
                                                          && (next_potential_divider_square <= N);
        static const bool   current_check                 = N % potential_divider != 0;
        static const bool   next_checks                   = IsPrimeHelper<N, next_potential_divider, next_done>::value;
        static const bool   value                         = current_check && next_checks;
    };

    template<size_t N, size_t potential_divider>
    struct IsPrimeHelper<N, potential_divider, true> {
        static const bool value = N != 1;
    };

    template<size_t N, size_t current_rounding_result, bool done>
    struct RoundToPowerOfTwoHelper {
        static const size_t next_rounding_result = 2 * current_rounding_result;
        static const size_t value = RoundToPowerOfTwoHelper<N, next_rounding_result, (next_rounding_result >= N)>::value;
    };

    template<size_t N, size_t current_rounding_result>
    struct RoundToPowerOfTwoHelper<N, current_rounding_result, true> {
        static const size_t value = current_rounding_result;
    };
}

template<size_t N>
struct IsPrime {
    static const bool value = IsPrimeHelper<N, 2, 2 * 2 <= N>::value;
};

template<size_t N>
const bool is_prime_v = IsPrime<N>::value;

template<size_t N>
struct RoundToPowerOfTwo {
    static const size_t value = RoundToPowerOfTwoHelper<N, 1, (1 >= N)>::value;
};

template<size_t N>
const size_t round_to_power_of_two_v = RoundToPowerOfTwo<N>::value;

template<size_t M, size_t N, size_t K>
struct MaxOfThree {
    static const size_t value = std::max(std::max(M, N), K);
};

template<size_t M, size_t N, size_t K>
const size_t max_of_three_v = MaxOfThree<M, N, K>::value;

template<size_t N>
class Residue {
private:
    size_t value_ = 0;

    static size_t sum(size_t lhs, size_t rhs) {
        lhs += rhs;
        if (lhs < rhs || lhs >= N) {
            lhs -= N;
        }
        return lhs;
    }

    static size_t mul(size_t lhs, size_t rhs) {
        // Implementation isn't trivial since lhs * rhs may simply be
        // greater that maximum value of size_t
        size_t result = 0;
        size_t addition = lhs;
        for (size_t factor = rhs; factor != 0; factor >>= 1) {
            if (factor & 1) {
                result = sum(result, addition);
            }
            addition = sum(addition, addition);
        }
        return result;
    }

    static size_t oppositeByAddition(size_t value) {
        return value == 0 ? 0 : N - value;
    }

    static size_t power(size_t value, size_t power_value) {
        if (power_value == 0) {
            return 1;
        }
        size_t power_half = power(value, power_value >> 1);
        size_t power_half_square = mul(power_half, power_half);
        return mul(power_half_square, power_value & 1 ? value : 1);
    }

    static size_t inverseByMultiplication(size_t value) {
        return power(value, N - 2);
    }

    static size_t calculateDeduction(int value) {
        size_t abs_deduction = std::abs(value) % N;
        return value < 0 ? N - abs_deduction : abs_deduction;
    }

public:
    Residue(int value = 0): value_(calculateDeduction(value)) {}

    Residue& operator+=(const Residue& that) {
        value_ = sum(value_, that.value_);
        return *this;
    }

    Residue& operator-=(const Residue& that) {
        value_ = sum(value_, oppositeByAddition(that.value_));
        return *this;
    }

    Residue& operator*=(const Residue& that) {
        value_ = mul(value_, that.value_);
        return *this;
    }

    Residue& operator/=(const Residue& that) {
        static_assert(is_prime_v<N>, "Division by modulo that isn't prime");
        return operator*=(inverseByMultiplication(that.value_));
    }

    explicit operator int() const {
        return static_cast<int>(value_);
    }

    explicit operator size_t() const {
        return value_;
    }

    bool operator==(const Residue&) const = default;
};

template<size_t N>
Residue<N> operator+(const Residue<N>& lhs, const Residue<N>& rhs) {
    Residue<N> result = lhs;
    return result += rhs;
}

template<size_t N>
Residue<N> operator-(const Residue<N>& lhs, const Residue<N>& rhs) {
    Residue<N> result = lhs;
    return result -= rhs;
}

template<size_t N>
Residue<N> operator*(const Residue<N>& lhs, const Residue<N>& rhs) {
    Residue<N> result = lhs;
    return result *= rhs;
}

template<size_t N>
Residue<N> operator/(const Residue<N>& lhs, const Residue<N>& rhs) {
    Residue<N> result = lhs;
    return result /= rhs;
}

template<size_t N>
std::ostream& operator<<(std::ostream& output, const Residue<N>& residue) {
    return output << static_cast<size_t>(residue);
}

template<size_t M, size_t N, typename Field>
class Matrix;

template<size_t M, size_t N, size_t K, typename Field>
Matrix<M, K, Field> operator*(const Matrix<M, N, Field>&, const Matrix<N, K, Field>&);

template<size_t M, size_t N, typename Field=Rational>
class Matrix {
private:
    std::array<std::array<Field, N>, M> elements_{};

public:
    Matrix() {}

    Matrix(std::initializer_list<std::initializer_list<Field>> elements) {
        size_t row_i = 0;
        for (const std::initializer_list<Field>& row: elements) {
            size_t col_i = 0;
            for (const Field& element : row) {
                elements_[row_i][col_i] = element;
                ++col_i;
            }
            ++row_i;
        }

    }

    void dumpTo(std::ostream& output) const {
        forEachCell(*this, [&output](const Field& cell, size_t, size_t col) {
            if (col != 0) {
                output << " ";
            }
            output << cell;
            if (col == N - 1) {
                output << '\n';
            }
        });
    }

    static Matrix Identity() {
        Matrix result;
        return forEachCell(result, [](Field& cell, size_t row, size_t col) {
                cell = Field(row == col);
               });
    }

    using CellProcessor = std::function<void (Field& cell, size_t row, size_t col)>;
    static Matrix& forEachCell(Matrix& matrix, const CellProcessor& cell_processor) {
        for (size_t row = 0; row < M; ++row) {
            for (size_t col = 0; col < N; ++col) {
                cell_processor(matrix[row][col], row, col);
            }
        }
        return matrix;
    }

    using ConstantCellProcessor = std::function<void (const Field&, size_t, size_t)>;
    static const Matrix& forEachCell(const Matrix& matrix, const ConstantCellProcessor& cell_processor) {
        for (size_t row = 0; row < M; ++row) {
            for (size_t col = 0; col < N; ++col) {
                cell_processor(matrix[row][col], row, col);
            }
        }
        return matrix;
    }

    using RowSubstractor   = std::function<void (Matrix&,
            size_t row_destination, size_t row_source, Field substraction_coefficient)>;
    using RowSwapper       = std::function<void (Matrix&, size_t row1, size_t row2)>;
    using RowMultiplicator = std::function<void (Matrix&, size_t row, const Field& coefficient)>;

    static void substractRow(Matrix& matrix,
            size_t row_destination, size_t row_source, Field substraction_coefficient) {
        for (size_t col = 0; col < N; ++col) {
            matrix[row_destination][col] -= substraction_coefficient * matrix[row_source][col];
        }
    }

    static void swapRows(Matrix& matrix, size_t row1, size_t row2) {
        std::swap(matrix[row1], matrix[row2]);
    }

    static void multiplyRow(Matrix& matrix, size_t row, const Field& coefficient) {
        for (Field& row_element : matrix[row]) {
            row_element *= coefficient;
        }
    }

    static Matrix& GaussMethod(Matrix& matrix,
            const RowSubstractor&   row_substractor,
            const RowSwapper&       row_swapper,
            const RowMultiplicator& row_multiplicator) {
        size_t leader_row = 0;
        for (size_t col = 0; leader_row < M && col < N; ++col) {
            for (size_t row = leader_row; row < M; ++row) {
                if (matrix[row][col] != Field(0)) {
                    row_swapper(matrix, leader_row, row);
                    break;
                }
            }
            if (matrix[leader_row][col] == Field(0)) {
                continue;
            }
            row_multiplicator(matrix, leader_row, Field(1) / matrix[leader_row][col]);
            for (size_t row = 0; row < M; ++row) {
                if (row != leader_row) {
                    row_substractor(matrix, row, leader_row, matrix[row][col]);
                }
            }
            ++leader_row;
        }
        return matrix;
    }

    using RowT = std::array<Field, N>;
    using ColT = std::array<Field, M>;

    static bool isZeroRow(const RowT& row) {
        return std::all_of(row.begin(), row.end(),
                [](const Field& row_element) { return row_element == 0; });
    }

    Matrix& operator+=(const Matrix& that) {
        return forEachCell(*this, [&that](Field& cell, size_t row, size_t col) {
                cell += that[row][col];
            });
    }

    Matrix& operator-=(const Matrix& that) {
        return forEachCell(*this, [&that](Field& cell, size_t row, size_t col) {
                cell -= that[row][col];
            });
    }

    Matrix& operator*=(const Matrix& that) {
        return *this = (*this * that);
    }

    Matrix& operator*=(Field coefficient) {
        return forEachCell(*this, [&coefficient](Field& cell, size_t, size_t) {
                cell *= coefficient;
            });
    }

    RowT& operator[](size_t row_i) {
        return elements_[row_i];
    }

    const RowT& operator[](size_t row_i) const {
        return elements_[row_i];
    }

    Field det() const {
        static_assert(M == N, "Unable to calculate determinant of nonsquare matrix");
        Field result = 1;
        Matrix tmp = *this;
        RowSwapper row_swapper = [&result](Matrix& matrix, size_t row1, size_t row2) {
            swapRows(matrix, row1, row2);
            if (row1 != row2) {
                result *= Field(-1);
            }
        };
        RowMultiplicator row_multiplicator = [&result](Matrix& matrix,
                size_t row, Field coefficient) {
            multiplyRow(matrix, row, coefficient);
            result /= coefficient;
        };
        GaussMethod(tmp, substractRow, row_swapper, row_multiplicator);
        return isZeroRow(tmp.getRow(N - 1)) ? 0 : result;
    }

    struct InversionError: public std::logic_error {
        using std::logic_error::logic_error;
    };

    Matrix& invert() {
        static_assert(M == N, "Unable to invert nonsquare matrix");
        Matrix result = Identity();
        RowSubstractor row_substractor = [&result](Matrix& matrix, size_t row_destination, size_t row_source, Field coefficient) {
            substractRow(matrix, row_destination, row_source, coefficient);
            substractRow(result, row_destination, row_source, coefficient);
        };
        RowSwapper row_swapper = [&result](Matrix& matrix, size_t row1, size_t row2) {
            swapRows(matrix, row1, row2);
            swapRows(result, row1, row2);
        };
        RowMultiplicator row_multiplicator = [&result](Matrix& matrix, size_t row, Field coefficient) {
            multiplyRow(matrix, row, coefficient);
            multiplyRow(result, row, coefficient);
        };
        GaussMethod(*this, row_substractor, row_swapper, row_multiplicator);
        if (isZeroRow(getRow(N - 1))) {
            throw InversionError("Inversion of degenerate matrix");
        }
        return *this = result;
    }

    Matrix inverted() const {
        Matrix result = *this;
        return result.invert();
    }

    size_t rank() const {
        Matrix tmp = *this;
        GaussMethod(tmp, substractRow, swapRows, multiplyRow);
        return static_cast<size_t>(
                std::count_if(tmp.elements_.begin(), tmp.elements_.end(),
                    [](const RowT& row) { return !isZeroRow(row); }));
    }

    Matrix<N, M, Field> transposed() const {
        Matrix<N, M, Field> result;
        forEachCell(*this, [&result](const Field& cell, size_t row, size_t col) {
                result[col][row] = cell;
            });
        return result;
    }

    RowT getRow(size_t row) const {
        return operator[](row);
    }

    ColT getColumn(size_t col) const {
        return transposed().getRow(col);
    }

    bool validIndices(size_t row, size_t col) const {
        return row < M && col < N;
    }

    bool operator==(const Matrix&) const = default;

    Field trace() const {
        static_assert(M == N, "Unable to calculate a trace of nonsquare matrix");
        Field result = 0;
        for (size_t i = 0; i < M; ++i) {
            result += (*this)[i][i];
        }
        return result;
    }
};

template<size_t N, typename Field=Rational>
using SquareMatrix = Matrix<N, N, Field>;

namespace {
    template<size_t N, typename Field>
    //NOLINTNEXTLINE
    using FourMatrixBlocks = std::array<SquareMatrix<N, Field>, 4>;

    template<size_t N, typename Field>
    FourMatrixBlocks<N / 2, Field> splitIntoFourBlocks(const SquareMatrix<N, Field>& matrix) {
        static const size_t BlockSize = N / 2;
        FourMatrixBlocks<BlockSize, Field> result;
        SquareMatrix<N, Field>::forEachCell(matrix, [&result](const Field& cell, size_t row, size_t col) {
                size_t block_index = 2 * (row / BlockSize) + col / BlockSize;
                size_t block_row = row % BlockSize;
                size_t block_col = col % BlockSize;
                result[block_index][block_row][block_col] = cell;
            });
        return result;
    }

    template<size_t N, typename Field>
    SquareMatrix<N * 2, Field> composeFourBlocks(const FourMatrixBlocks<N, Field>& blocks) {
        SquareMatrix<N * 2, Field> result;
        SquareMatrix<N * 2, Field>::forEachCell(result, [&blocks](Field& cell, size_t row, size_t col) {
                size_t block_index = 2 * (row / N) + col / N;
                size_t block_row = row % N;
                size_t block_col = col % N;
                cell = blocks[block_index][block_row][block_col];
            });
        return result;
    }

    template<size_t N, typename Field>
    SquareMatrix<N, Field> StrassenMulImpl(const SquareMatrix<N, Field>& a, const SquareMatrix<N, Field>& b) {
        // Designations are taken from
        // https://en.wikipedia.org/wiki/Strassen_algorithm
        if constexpr (N == 1) {
            return { { a[0][0] * b[0][0] } };
        } else {
            auto [a11, a12, a21, a22] = splitIntoFourBlocks(a);
            auto [b11, b12, b21, b22] = splitIntoFourBlocks(b);

            Matrix m1 = (a11 + a22) * (b11 + b22);
            Matrix m2 = (a21 + a22) *  b11;
            Matrix m3 =  a11        * (b12 - b22);
            Matrix m4 =  a22        * (b21 - b11);
            Matrix m5 = (a11 + a12) *  b22;
            Matrix m6 = (a21 - a11) * (b11 + b12);
            Matrix m7 = (a12 - a22) * (b21 + b22);
            FourMatrixBlocks<N / 2, Field> resulting_blocks{m1 + m4 - m5 + m7, m3 + m5, m2 + m4, m1 - m2 + m3 + m6};
            return composeFourBlocks(resulting_blocks);
        }
    }

    template<size_t NewM, size_t NewN, size_t M, size_t N, typename Field>
    Matrix<NewM, NewN, Field> resizeMatrix(const Matrix<M, N, Field>& matrix) {
        Matrix<NewM, NewN, Field> result;
        Matrix<M, N, Field>::forEachCell(matrix, [&result](const Field& cell, size_t row, size_t col) {
                if (result.validIndices(row, col)) {
                    result[row][col] = cell;
                }
            });
        return result;
    }
}

template<size_t M, size_t N, size_t K, typename Field>
Matrix<M, K, Field> StrassenMul(const Matrix<M, N, Field>& lhs, const Matrix<N, K, Field>& rhs) {
    static const size_t StrassenSize = max_of_three_v<round_to_power_of_two_v<M>,
                 round_to_power_of_two_v<N>, round_to_power_of_two_v<K>>;

    using RoundedMatrix       = SquareMatrix<StrassenSize, Field>;
    RoundedMatrix lhs_rounded = resizeMatrix<StrassenSize, StrassenSize>(lhs);
    RoundedMatrix rhs_rounded = resizeMatrix<StrassenSize, StrassenSize>(rhs);
    RoundedMatrix result      = StrassenMulImpl(lhs_rounded, rhs_rounded);
    return resizeMatrix<M, K>(result);
}

template<size_t M, size_t N, typename Field>
Matrix<M, N, Field> operator+(const Matrix<M, N, Field>& lhs, const Matrix<M, N, Field>& rhs) {
    Matrix<M, N, Field> result = lhs;
    return result += rhs;
}

template<size_t M, size_t N, typename Field>
Matrix<M, N, Field> operator-(const Matrix<M, N, Field>& lhs, const Matrix<M, N, Field>& rhs) {
    Matrix<M, N, Field> result = lhs;
    return result -= rhs;
}

template<size_t M, size_t N, size_t K, typename Field>
Matrix<M, K, Field> operator*(const Matrix<M, N, Field>& lhs, const Matrix<N, K, Field>& rhs) {
    return StrassenMul(lhs, rhs);
}

template<size_t M, size_t N, typename Field>
Matrix<M, N, Field> operator*(const Field& coefficient, Matrix<M, N, Field> matrix) {
    return matrix *= coefficient;
}

template<size_t M, size_t N, typename Field>
Matrix<M, N, Field> operator*(Matrix<M, N, Field> matrix, const Field& coefficient) {
    return matrix *= coefficient;
}

template<size_t M, size_t N, typename Field>
std::ostream& operator<<(std::ostream& output, const Matrix<M, N, Field>& matrix) {
    matrix.dumpTo(output);
    return output;
}

