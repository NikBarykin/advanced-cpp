#pragma once

#include <iostream>
#include <cstring>
#include <algorithm>


class String {
private:
    size_t size_ = 0;
    size_t capacity_ = 0;
    char* data_ = nullptr;

    static char* allocate(size_t n) {
        return new char[n];
    }

    void reallocate(size_t new_capacity) {
        char *new_data = allocate(new_capacity + 1);
        std::strcpy(new_data, data_);
        delete[] data_;
        data_ = new_data;
        capacity_ = new_capacity; 
    }

    void reserve(size_t target_size) {
        if (target_size > capacity_) {
            reallocate(target_size);
        }
    }

    void set_null_terminator() {
        data_[size_] = '\0';
    }

public:
    String(size_t n, char c)
    : size_(n)
    , capacity_(n)
    , data_(allocate(capacity_ + 1))
    {
        std::fill(data_, data_ + size_, c);
        set_null_terminator();
    }

    String(const char* str)
    : size_(std::strlen(str))
    , capacity_(size_)
    , data_(allocate(capacity_ + 1))
    {
        std::strcpy(data_, str);
    }

    String(): String("") {}

    explicit String(char c): String(1, c) {}

    String(const String& other)
    : size_(other.size())
    , capacity_(other.capacity_)
    , data_(allocate(capacity_ + 1))
    {
        std::strcpy(data_, other.data());
    }

    String& operator=(const String& other) {
        if (this != &other) {
            reserve(other.size());
            std::strcpy(data_, other.data());
            size_ = other.size();
        }
        return *this;
    }

    char &operator[] (size_t i) {
        return data_[i];
    }

    const char& operator[] (size_t i) const {
        return data_[i];
    }

    size_t size() const {
        return size_;
    }
    
    size_t capacity() const {
        return capacity_;
    }

    size_t length() const {
        return size();
    }

    char* data() {
        return data_;
    }

    const char* data() const {
        return data_;
    } 
    
    void push_back(char c) {
        if (size_ == capacity_) {
            reallocate(2 * capacity_ + 1);
        }
        data_[size_++] = c;
        set_null_terminator(); 
    }

    void pop_back() {
        --size_;
        set_null_terminator();
    }
    
    char& front() {
        return operator[](0);
    }

    const char& front() const {
        return operator[](0);
    }

    char& back() {
        return operator[](size_ - 1);
    }

    const char& back() const {
        return operator[](size_ - 1);
    }
    
    String& operator +=(const String& other) {
        size_t new_size = size_ + other.size();
        reserve(new_size);
        std::strcpy(data_ + size_, other.data());
        size_ = new_size;
        return *this;
    }

    String& operator +=(char c) {
        push_back(c); 
        return *this;
    }
 
    String substr(size_t start, size_t count) const {
        String result(count, '\0');
        std::copy(data_ + start, data_ + start + count, result.data());
        return result; 
    }

private:
    bool substring_matches(const String& substring, size_t start_position) const {
        return std::strncmp(data_ + start_position, 
                substring.data(), substring.size()) == 0;
    }

public:
    size_t find(const String& substring) const {
        for (size_t i = 0; i + substring.size() <= size_; ++i) {
            if (substring_matches(substring, i)) {
                return i;
            }
        } 
        return size_;
    }
    
    size_t rfind(const String& substring) const {
        for (size_t i = size_; i >= substring.size(); --i) {
            if (substring_matches(substring, i - substring.size())) {
                return i - substring.size();
            }
            
        }
        return size_;
    }
    
    bool empty() const {
        return size_ == 0;
    }

    void clear() {
        size_ = 0;
        set_null_terminator();
    }

    void shrink_to_fit() {
        reallocate(size_);
    }

    ~String() {
        delete[] data_;
    }
};

String operator+(String lhs, const String& rhs) {
    return lhs += rhs;
}

String operator+(char c, const String& rhs) {
    String result(c);
    return result += rhs; 
}

String operator+(String lhs, char c) {
    return lhs += c;
}

bool operator ==(const String& lhs, const String& rhs) {
    return lhs.size() == rhs.size() && 
            std::strcmp(lhs.data(), rhs.data()) == 0;
}

bool operator !=(const String& lhs, const String& rhs) {
    return !(lhs == rhs);
}

bool operator <(const String& lhs, const String& rhs) {
    return std::strcmp(lhs.data(), rhs.data()) < 0;
}


bool operator >(const String& lhs, const String& rhs) {
    return rhs < lhs;
}

bool operator <=(const String& lhs, const String& rhs) {
    return !(rhs < lhs);
}

bool operator >=(const String& lhs, const String& rhs) {
    return rhs <= lhs;
}

std::ostream& operator<< (std::ostream &output, const String& str) {
    return output << str.data();
}

std::istream& operator>> (std::istream& input, String& str) {
    str.clear();
    while (true) {
        char c = input.get();
        if (c == std::istream::traits_type::eof() || std::isspace(c)) {
            break;
        }
        str.push_back(c);
    }
    return input;
}

