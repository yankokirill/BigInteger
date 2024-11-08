#include <algorithm>
#include <complex>
#include <iostream>
#include <vector>

namespace {
    const long double pi = 2 * asinl(1);

    size_t to_pow2(size_t n) {
        size_t m = 1;
        while (m < n) {
            m *= 2;
        }
        return m;
    }

    void fft(std::vector<std::complex<long double>>& digits, bool invert) {
        for (size_t i = 1, j = 0; i < digits.size(); ++i) {
            size_t bit = digits.size() >> 1;
            for (; j >= bit; bit >>= 1) {
                j -= bit;
            }
            j += bit;
            if (i < j) {
                swap(digits[i], digits[j]);
            }
        }

        for (size_t len = 2; len <= digits.size(); len *= 2) {
            long double ang = 2 * pi / static_cast<long double>(len);
            if (invert)
                ang = -ang;
            std::complex<long double> w_len(cosl(ang), sinl(ang));
            for (size_t i = 0; i < digits.size(); i += len) {
                std::complex<long double> w(1);
                for (size_t j = 0; j < len / 2; ++j) {
                    std::complex<long double> u = digits[i + j];
                    std::complex<long double> v = digits[i + j + len / 2] * w;
                    digits[i + j] = u + v;
                    digits[i + j + len / 2] = u - v;
                    w *= w_len;
                }
            }
        }
        if (invert) {
            long double n = digits.size();
            for (auto& digit : digits) {
                digit /= n;
            }
        }
    }
}

class BigInteger;
BigInteger multiply(BigInteger, long long);

class BigInteger {
private:

    static const long long REAL_BASE = 1e3;
    static const long long USER_BASE = 10;
    static const size_t DIGIT_SIZE = 3;

    std::vector<long long> digits;
    bool is_negative;

    void deleteZeroes() {
        while (digits.size() > 1 && digits.back() == 0) {
            digits.pop_back();
        }
        if (!*this) {
            is_negative = false;
        }
    }

    void toCarry() {
        long long carry = 0;
        for (auto& digit : digits) {
            digit += carry;
            carry = digit / REAL_BASE;
            digit %= REAL_BASE;
        }
        if (carry) {
            digits.push_back(carry);
        }
    }

public:

    void multiply(long long x) {
        is_negative = false;
        for (auto& digit : digits) {
            digit *= x;
        }
        toCarry();
        deleteZeroes();
    }

    BigInteger(): digits(1), is_negative(false) {}
    BigInteger(long long x) : is_negative(x < 0) {
        if (x == 0) {
            digits.resize(1);
            return;
        }
        if (is_negative) {
            x = -x;
        }
        while (x) {
            digits.push_back(x % REAL_BASE);
            x /= REAL_BASE;
        }
    }

    void swap(BigInteger& x) {
        std::swap(digits, x.digits);
        std::swap(is_negative, x.is_negative);
    }

    explicit operator bool() const {
        return digits.size() != 1 || digits[0] != 0;
    }

    void applyAbs() {
        is_negative = false;
    }
    void changeSign() {
        if (*this) {
            is_negative = !is_negative;
        }
    }


    BigInteger operator+() const {
        return *this;
    }
    BigInteger operator-() const {
        BigInteger copy = *this;
        copy.changeSign();
        return copy;
    }

    BigInteger& operator+=(const BigInteger& x) {
        if (x.is_negative == is_negative) {
            if (x.digits.size() > digits.size()) {
                digits.resize(x.digits.size());
            }
            long long carry = 0;
            for (size_t i = 0; i < x.digits.size(); ++i) {
                digits[i] += x.digits[i] + carry;
                carry = digits[i] >= REAL_BASE;
                if (carry) {
                    digits[i] -= REAL_BASE;
                }
            }

            if (carry) {
                size_t i = x.digits.size();
                while (i < digits.size() && digits[i] + 1 == REAL_BASE) {
                    digits[i] = 0;
                    ++i;
                }
                if (i == digits.size()) {
                    digits.push_back(0);
                }
                ++digits[i];
            }
        } else {
            if (x.digits.size() >= digits.size()) {
                digits.resize(x.digits.size());
                size_t i = x.digits.size() - 1;
                for (; i > 0 && digits[i] == x.digits[i]; --i) {
                    digits.pop_back();
                }
                is_negative ^= digits[i] < x.digits[i];
            }

            long long carry = 0;
            long long sign = 1 - 2 * (is_negative == x.is_negative);
            for (size_t i = 0; i < x.digits.size(); ++i) {
                digits[i] = sign * (digits[i] - x.digits[i]) - carry;
                carry = digits[i] < 0;
                if (carry) {
                    digits[i] += REAL_BASE;
                }
            }
            if (carry) {
                size_t i = x.digits.size();
                while (digits[i] == 0) {
                    digits[i] = REAL_BASE - 1;
                    ++i;
                }
                --digits[i];
            }
            deleteZeroes();
        }
        return *this;
    }

    BigInteger& operator++() {
        return *this += 1;
    }
    BigInteger operator++(int) {
        BigInteger tmp = *this;
        ++*this;
        return tmp;
    }

    BigInteger& operator-=(const BigInteger& x) {
        changeSign();
        *this += x;
        changeSign();
        return *this;
    }
    BigInteger& operator--() {
        return *this += -1;
    }
    BigInteger operator--(int) {
        BigInteger tmp = *this;
        --*this;
        return tmp;
    }

    BigInteger& operator*=(const BigInteger& x) {
        size_t n = to_pow2(digits.size() + x.digits.size());
        std::vector<std::complex<long double>> fa(n);
        std::vector<std::complex<long double>> fb(n);
        for (size_t i = 0; i < digits.size(); ++i) {
            fa[i] = digits[i];
        }
        for (size_t i = 0; i < x.digits.size(); ++i) {
            fb[i] = x.digits[i];
        }

        fft(fa, false);
        fft (fb, false);
        for (size_t i = 0; i < n; ++i) {
            fa[i] *= fb[i];
        }
        fft (fa, true);

        digits.resize(n);
        for (size_t i = 0; i < n; ++i) {
            digits[i] = static_cast<long long>(roundl(fa[i].real()));
        }

        toCarry();
        is_negative ^= x.is_negative;
        deleteZeroes();
        return *this;
    }

    void multiply_pow10(size_t q) {
        if (*this) {
            digits.insert(digits.begin(), q / DIGIT_SIZE, 0);
            if (q %= DIGIT_SIZE) {
                long long x = USER_BASE;
                while (--q) {
                    x *= USER_BASE;
                }
                multiply(x);
            }
        }
    }

    std::pair<BigInteger, BigInteger> div_mod(const BigInteger& x) const {
        BigInteger div;
        BigInteger mod;
        for (size_t i = digits.size() - 1; i < digits.size(); --i) {
            if (mod.digits.back()) {
                mod.digits.insert(mod.digits.begin(), 1, digits[i]);
            } else {
                mod.digits[0] = digits[i];
            }
            div.digits.push_back(0);

            if (mod >= x) {
                long long &left = div.digits.back();
                long long right = REAL_BASE;
                while (left + 1 < right) {
                    long long md = (left + right) / 2;
                    if (::multiply(x, md) <= mod) {
                        left = md;
                    } else {
                        right = md;
                    }
                }
                mod -= ::multiply(x, left);
            }
        }
        reverse(div.digits.begin(), div.digits.end());
        div.is_negative = is_negative ^ x.is_negative;
        mod.is_negative = mod && is_negative;
        div.deleteZeroes();
        return {div, mod};
    }

    BigInteger& operator/=(const BigInteger& x) {
        return *this = div_mod(x).first;
    }

    BigInteger& operator%=(const BigInteger& x) {
        return *this = div_mod(x).second;
    }


    bool operator==(const BigInteger&) const = default;
    friend std::strong_ordering operator<=>(const BigInteger& x, const BigInteger& y) {
        std::strong_ordering less = std::strong_ordering::less;
        std::strong_ordering equal = std::strong_ordering::equal;
        std::strong_ordering greater = std::strong_ordering::greater;

        if (x.is_negative && !y.is_negative) {
            return less;
        }
        if (!x.is_negative && y.is_negative) {
            return greater;
        }
        if (x.is_negative) {
            std::swap(less, greater);
        }
        if (x.digits.size() < y.digits.size()) {
            return less;
        }
        if (x.digits.size() > y.digits.size()) {
            return greater;
        }

        size_t i = x.digits.size() - 1;
        while (i < x.digits.size() && x.digits[i] == y.digits[i]) {
            --i;
        }
        if (i > x.digits.size()) {
            return equal;
        }

        return x.digits[i] < y.digits[i] ? less : greater;
    }

    std::string toString() const {
        std::string s(DIGIT_SIZE * digits.size(), '\0');
        for (size_t i = 0; i < digits.size(); ++i) {
            long long t = digits[i];
            for (size_t j = DIGIT_SIZE * i; j < DIGIT_SIZE * (i + 1); ++j) {
                s[j] = std::to_string(t % USER_BASE)[0];
                t /= USER_BASE;
            }
        }
        while (s.size() > 1 && s.back() == '0') {
            s.pop_back();
        }
        if (is_negative) {
            s.push_back('-');
        }
        reverse(s.begin(), s.end());
        return s;
    }

    friend std::istream& operator>>(std::istream& in, BigInteger& x) {
        std::string s;
        in >> s;
        reverse(s.begin(), s.end());
        if (s.back() == '-') {
            x.is_negative = true;
            s.pop_back();
        } else {
            x.is_negative = false;
        }
        while (s.size() % DIGIT_SIZE) {
            s.push_back('0');
        }
        x.digits.resize(s.size() / DIGIT_SIZE);

        for (size_t i = 0; i < x.digits.size(); ++i) {
            x.digits[i] = 0;
            for (size_t j = DIGIT_SIZE * (i + 1); j > DIGIT_SIZE * i; --j) {
                x.digits[i] = USER_BASE * x.digits[i] + (s[j - 1] - '0');
            }
        }
        x.deleteZeroes();
        return in;
    }

};

BigInteger multiply(BigInteger ans, long long x) {
    ans.multiply(x);
    return ans;
}

std::ostream& operator<<(std::ostream& out, const BigInteger& x) {
    return out << x.toString();
}
BigInteger operator"" _bi(unsigned long long n) {
    return BigInteger(static_cast<long long>(n));
}

BigInteger operator+(BigInteger x, const BigInteger& y) {
    x += y;
    return x;
}
BigInteger operator-(BigInteger x, const BigInteger& y) {
    x -= y;
    return x;
}
BigInteger operator*(BigInteger x, const BigInteger& y) {
    x *= y;
    return x;
}
BigInteger operator/(BigInteger x, const BigInteger& y) {
    x /= y;
    return x;
}
BigInteger operator%(BigInteger x, const BigInteger& y) {
    x %= y;
    return x;
}


BigInteger gcd(BigInteger a, BigInteger b) {
    a.applyAbs();
    b.applyAbs();

    while (b) {
        a %= b;
        a.swap(b);
    }
    return a;
}

class Rational {
private:
    static const size_t MANTISSA_SIZE = 20;
    BigInteger x;
    BigInteger y;

    void reduce() {
        if (y < 0) {
            x.changeSign();
            y.changeSign();
        }
        BigInteger g = gcd(x, y);
        x /= g;
        y /= g;
    }
public:
    Rational(const BigInteger& x): x(x), y(1) {}
    Rational(const BigInteger& x, const BigInteger& y): x(x), y(y) {
        reduce();
    }

    Rational(long long x) : x(x), y(1) {}
    Rational(long long x, long long y) : x(x), y(y) {
        reduce();
    }
    Rational() : x(0), y(1) {}

    explicit operator double() const {
        return atof(asDecimal(MANTISSA_SIZE).c_str());
    }

    Rational operator+() const {
        return *this;
    }
    Rational operator-() const {
        Rational copy(*this);
        copy.x.changeSign();
        return copy;
    }

    Rational& operator+=(const Rational& t) {
        x *= t.y;
        x += t.x * y;
        y *= t.y;
        reduce();
        return *this;
    }
    Rational& operator-=(const Rational& t) {
        x.changeSign();
        *this += t;
        x.changeSign();
        return *this;
    }

    Rational& operator*=(const Rational& t) {
        x *= t.x;
        y *= t.y;
        reduce();
        return *this;
    }
    Rational& operator/=(const Rational& t) {
        x *= t.y;
        y *= t.x;
        reduce();
        return *this;
    }

    bool operator==(const Rational&) const = default;
    friend std::strong_ordering operator<=>(const Rational& digits, const Rational& b) {
        return digits.x * b.y <=> b.x * digits.y;
    }

    std::string toString() const {
        return x.toString() + (y != 1_bi ? '/' + y.toString() : "");
    }

    std::string asDecimal(size_t precision=0) const {
        auto [div, mod] = x.div_mod(y);
        std::string integer = div.toString();
        if (precision == 0) {
            return integer;
        }
        mod.applyAbs();
        mod.multiply_pow10(precision);
        mod /= y;
        std::string s = mod.toString();
        if (integer == "0" && x < 0 && mod) {
            integer = "-0";
        }
        return integer + '.' + std::string(precision - s.size(), '0') + s;
    }
};

Rational operator+(Rational a, const Rational& b) {
    a += b;
    return a;
}
Rational operator-(Rational a, const Rational& b) {
    a -= b;
    return a;
}
Rational operator*(Rational a, const Rational& b) {
    a *= b;
    return a;
}
Rational operator/(Rational a, const Rational& b) {
    a /= b;
    return a;
}