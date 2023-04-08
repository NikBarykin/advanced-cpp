#include <array>
#include <algorithm>
#include <ctime>
#include <initializer_list>
#include <iostream>
#include <cstdlib>
#include <numeric>
#include <math.h>
#include <sched.h>
#include <vector>
#include <cassert>
#include <optional>
#include <cmath>
#include <functional>


int mathSignum(double x) {
    return x == 0 ? 0 : static_cast<int>(x / std::abs(x));
}

bool doublesEqual(double a, double b, const double eps = 1e-6) {
    return std::abs(a - b) < eps;
}

double degreesToRadians(double angle_in_degress) {
    static const int degrees_in_pi = 180;
    return angle_in_degress * M_PI / degrees_in_pi;
}

struct Point {
    double x;
    double y;
    Point(double x, double y): x(x), y(y) {}

    Point& operator+=(const Point& that) {
        x += that.x;
        y += that.y;
        return *this;
    }

    Point& operator-=(const Point& that) {
        return *this += -that;
    }

    Point operator-() const {
        return { -x, -y };
    }
};

bool operator==(const Point& lhs, const Point& rhs) {
    return doublesEqual(lhs.x, rhs.x) && doublesEqual(lhs.y, rhs.y);
}

Point operator+(const Point& lhs, const Point& rhs) {
    Point  result  = lhs;
    return result += rhs;
}

Point operator-(const Point& lhs, const Point& rhs) {
    Point  result  = lhs;
    return result -= rhs;
}

Point operator*(double lambda, const Point& point) {
    return { lambda * point.x, lambda * point.y };
}

Point operator*(const Point& point, double lambda) {
    return lambda * point;
}

Point operator/(const Point& point, double lambda) {
    return (1 / lambda) * point;
}

Point rotateVector(const Point& vector, double angle) {
    return { vector.x * std::cos(angle) - vector.y * std::sin(angle),
             vector.x * std::sin(angle) + vector.y * std::cos(angle) };
}

Point calculateSegmentMiddle(Point segment_start, Point segment_end) {
    //NOLINTNEXTLINE
    return (segment_start + segment_end) / 2;
}

Point rotatePoint(const Point& subject, const Point& center, double angle) {
    return center + rotateVector(subject - center, angle);
}

Point scalePoint(const Point& subject, const Point& center, double coefficient) {
    return center + coefficient * (subject - center);
}

Point reflectPoint(const Point& subject, const Point& reflection_center) {
    return scalePoint(subject, reflection_center, -1);
}

double crossProduct(Point a, Point b) {
    return a.x * b.y - a.y * b.x;
}

double dot_product(Point a, Point b) {
    return a.x * b.x + a.y * b.y;
}

double squared_modulo(Point p) {
    return dot_product(p, p);
}

double modulo(Point p) {
    return std::sqrt(squared_modulo(p));
}

double pointDistance(Point a, Point b) {
    return modulo(a - b);
}

double calculateAngle(Point a, Point b) {
    return std::atan2(crossProduct(a, b), dot_product(a, b));
}

Point getNormal(Point p) {
    return { -p.y, p.x };
}

class Line {
public:
    // a * x + b * y + c = 0
    double a;
    double b;
    double c;

    void normalize() {
        if (a != 0) {
            b /= a;
            c /= a;
            a /= a;
        } else {
            c /= b;
            b /= b;
        }
    }

    static Line constructByPointAndVector(const Point& p, const Point& vec) {
        return { p, p + vec };
    }

public:
    Line(const Point& p1, const Point& p2)
    : a(p2.y - p1.y), b(p1.x - p2.x), c(0 - a * p1.x - b * p1.y) {
        normalize();
    }

    Line(double slope, double shift)
    : a(slope), b(-1), c(shift) {
        normalize();
    }

    Line(const Point& p, double slope)
    : a(slope), b(-1), c(p.y - slope * p.x) {
        normalize();
    }
};

bool operator==(const Line& lhs, const Line& rhs) {
    return doublesEqual(lhs.a, rhs.a)
        && doublesEqual(lhs.b, rhs.b)
        && doublesEqual(lhs.c, rhs.c);
}

Point getNormal(const Line& l) {
    return { l.a, l.b };
}

double signedDistanceToLine(const Point& point, const Line& line) {
    return -(line.a * point.x + line.b * point.y + line.c) / squared_modulo(getNormal(line));
}

Point reflectPointByAxis(const Point& subject, const Line& line) {
    return subject + 2 * signedDistanceToLine(subject, line) * getNormal(line);
}

bool lineContainsPoint(const Line& line, const Point& point) {
    return doublesEqual(signedDistanceToLine(point, line), 0);
}

// Function acquires lines by value since it will probably swap them
Point intersectLines(Line l1, Line l2) {
    if (l1.a == 0) {
       std::swap(l1, l2);
    }
    double result_y = -(l2.c - l1.c * l2.a / l1.a) / (l2.b - l1.b * l2.a / l1.a);
    double result_x = -(l1.c + l1.b * result_y) / l1.a;
    return { result_x, result_y };
}

Line constructMiddleperpendicular(const Point& segment_start, const Point& segment_finish) {
    Point segment_middle = calculateSegmentMiddle(segment_start, segment_finish);
    Point line_direction = getNormal(segment_finish - segment_start);
    return Line::constructByPointAndVector(segment_middle, line_direction);
}

class Shape {
public:
    virtual double perimeter() const = 0;
    virtual double area() const = 0;
    virtual bool operator==(const Shape& that) const = 0;
    virtual bool isCongruentTo(const Shape& that) const = 0;
    virtual bool isSimilarTo(const Shape& that) const = 0;
    virtual bool containsPoint(const Point& point) const = 0;
    virtual Shape& rotate(const Point& center, double angle) = 0;
    virtual Shape& reflect(const Point& center) = 0;
    virtual Shape& reflect(const Line& axis) = 0;
    virtual Shape& scale(const Point& center, double coefficient) = 0;
    virtual ~Shape() = default;
};

class Polygon: public Shape {
public:
    using VerticesT = std::vector<Point>;
    using VertexConstIt = VerticesT::const_iterator;

private:
    VerticesT vertices_;

    VertexConstIt nextVertex(VertexConstIt it, size_t count = 1) const {
        while (count--) {
            it = ++it == vertices_.end() ? vertices_.begin() : it;
        }
        return it;
    }

public:
    size_t verticesCount() const {
        return vertices_.size();
    }

    const VerticesT& getVertices() const {
        return vertices_;
    }

    bool isConvex() const {
        auto get_angle_orientation = [this](VertexConstIt first_vertex_it) -> int {
            Point v1 = *first_vertex_it;
            Point v2 = *this->nextVertex(first_vertex_it, 1);
            Point v3 = *this->nextVertex(first_vertex_it, 2);
            return mathSignum(crossProduct(v1 - v2, v3 - v2));
        };

        int expected_orientation_of_polygon_angles = get_angle_orientation(getVertices().begin());
        for (VertexConstIt vertex_it = vertices_.cbegin(); vertex_it != vertices_.cend(); ++vertex_it) {
            if (expected_orientation_of_polygon_angles != get_angle_orientation(vertex_it)) {
                return false;
            }
        }
        return true;
    }

    Polygon(const VerticesT& vertices): vertices_(vertices) {}

    template<typename... Vertices>
    Polygon(Point p, Vertices... vertices): vertices_({p, vertices... }) {}

    Polygon(std::initializer_list<Point> points): vertices_(points) {}

    double perimeter() const override {
        double result = 0;
        for (VertexConstIt it = vertices_.cbegin(); it != vertices_.cend(); ++it) {
            result += pointDistance(*it, *nextVertex(it));
        }
        return result;
    }

    double area() const override {
        double result = 0;
        for (VertexConstIt it = vertices_.cbegin(); it != vertices_.cend(); ++it) {
            result += crossProduct(*it, *nextVertex(it)) / 2;
        }
        return std::abs(result);
    }

    bool operator==(const Shape& that) const override {
        Polygon const* that_p = dynamic_cast<Polygon const*>(&that);
        return that_p == nullptr ? false : *this == *that_p;
    }

private:
    typedef bool (*ComparePolygonsWithFixedIndexation)(const Polygon&, const Polygon&);
    static bool comparePolygonsForEachIndexation(const Polygon& poly1, const Polygon& poly2,
            const ComparePolygonsWithFixedIndexation& comparator) {
        if (poly1.verticesCount() != poly2.verticesCount()) {
            return false;
        }

        for (bool inverse_bypass_direction : { false, true }) {
            Polygon poly1_tmp = poly1;
            VerticesT& vertices1_tmp = poly1_tmp.vertices_;
            if (inverse_bypass_direction) {
                std::reverse(vertices1_tmp.begin(), vertices1_tmp.end());
            }
            for (size_t cyclic_shift = 0; cyclic_shift < poly1.verticesCount(); ++cyclic_shift) {
                std::rotate(vertices1_tmp.begin(), ++vertices1_tmp.begin(), vertices1_tmp.end());
                if (comparator(poly1_tmp, poly2)) {
                    return true;
                }
            }
        }

        return false;
    }

public:
    bool operator==(const Polygon& that) const {
        return comparePolygonsForEachIndexation(*this, that,
                [](const Polygon& poly1, const Polygon& poly2) {
                    return poly1.getVertices() == poly2.getVertices();
                });
    }

    bool isCongruentTo(const Shape& that) const override {
        Polygon const* that_p = dynamic_cast<Polygon const*>(&that);
        return that_p == nullptr ? false : isCongruentTo(*that_p);
    }

    bool isCongruentTo(const Polygon& that) const {
        ComparePolygonsWithFixedIndexation fixedIndexationCongruencyComparator =
            [](const Polygon& poly1, const Polygon& poly2) {
            for (bool reflect_polygon: { false, true }) {
                Polygon poly1_tmp = poly1;
                if (reflect_polygon) {
                    poly1_tmp.reflect(Line(0, 0));
                }

                const VerticesT& vertices1 = poly1_tmp.getVertices();
                const VerticesT& vertices2 = poly2.getVertices();

                Point shift_vector = vertices2.front() - vertices1.front();
                Point edge1 = vertices1[1] - vertices1.front();
                Point edge2 = vertices2[1] - vertices2.front();
                double rotate_angle = calculateAngle(edge1, edge2);

                poly1_tmp.shift(shift_vector);
                poly1_tmp.rotateRadians(poly1_tmp.getVertices().front(), rotate_angle);

                if (poly1_tmp.getVertices() == vertices2) {
                    return true;
                }
            }
            return false;
        };
        return comparePolygonsForEachIndexation(*this, that, fixedIndexationCongruencyComparator);
    }

    bool isSimilarTo(const Shape& that) const override {
        double simmilarity_coefficient = std::sqrt(that.area() / area());
        Polygon this_tmp = *this;
        this_tmp.scale(getVertices().front(), simmilarity_coefficient);
        return this_tmp.isCongruentTo(that);
    }

    bool containsPoint(const Point& point) const override {
        if (std::find(vertices_.begin(), vertices_.end(), point) != vertices_.end()) {
            return true;
        }
        double sum_of_oriented_angles = 0;
        for (VertexConstIt it = vertices_.cbegin(); it != vertices_.cend(); ++it) {
            Point vector1 = *nextVertex(it) - point;
            Point vector2 = *it             - point;
            double angle = calculateAngle(vector1, vector2);
            if (doublesEqual(std::abs(angle), M_PI)) {
                return true;
            }
            sum_of_oriented_angles += angle;
        }
        return doublesEqual(std::abs(sum_of_oriented_angles), 2 * M_PI);
    }

private:
    using PointTransformation = std::function<Point (const Point&)>;
    Polygon& transformPoints(const PointTransformation& transformation) {
        for (Point& point : vertices_) {
            point = transformation(point);
        }
        return *this;
    }

    template<typename TransformBasis, typename... TransformArgs>
    static PointTransformation bindPointTransformationArgs(
            TransformBasis transformation_basis, TransformArgs... transform_args) {
        using namespace std::placeholders;
        return std::bind(transformation_basis, _1, transform_args...);
    }

public:
    Polygon& shift(const Point& vector) {
        return transformPoints(bindPointTransformationArgs(operator+, vector));
    }

    Polygon& rotateRadians(const Point& center, double angle) {
        return transformPoints(bindPointTransformationArgs(rotatePoint, center, angle));
    }

    Polygon& rotate(const Point& center, double angle_in_degrees) override {
        return rotateRadians(center, degreesToRadians(angle_in_degrees));
    }

    Polygon& reflect(const Point& center) override {
        return transformPoints(bindPointTransformationArgs(reflectPoint, center));
    }

    Polygon& reflect(const Line& axis) override {
        return transformPoints(bindPointTransformationArgs(reflectPointByAxis, axis));
    }

    Polygon& scale(const Point& center, double coefficient) override {
        return transformPoints(bindPointTransformationArgs(scalePoint, center, coefficient));
    }
};


class Ellipse : public Shape {
private:
    Point focus1_;
    Point focus2_;
    double focal_dist_;

public:
    Ellipse(Point focus1, Point focus2, double focal_dist)
    : focus1_(focus1), focus2_(focus2), focal_dist_(focal_dist) {}
    // note: I implement methods using method "focuses" because I don't want
    // to use inner field structure

    std::pair<Point, Point> focuses() const {
        return { focus1_, focus2_ };
    }

    std::pair<Line, Line> directrices() const {
        double distance_from_center = majorAxis() / eccentricity();
        auto [focus1, focus2] = focuses();
        Point directrice_vector = getNormal(Line(focus1, focus2));
        Point focus_direction = (1.0 / 2 / focalParameter()) * (focus1 - focus2);
        Point directrice1_point = center() + distance_from_center * focus_direction;
        Point directrice2_point = center() - distance_from_center * focus_direction;
        return { Line::constructByPointAndVector(directrice1_point, directrice_vector),
                 Line::constructByPointAndVector(directrice2_point, directrice_vector) };
    }

    double focalParameter() const {
        return modulo(focuses().first - center());
    }

    double eccentricity() const {
        return focalParameter() / (focal_dist_ / 2);
    }

    Point center() const {
        auto [focus1, focus2] = focuses();
        return (focus1 + focus2) / 2;
    }

    double majorAxis() const {
        return focal_dist_ / 2;
    }

    double minorAxis() const {
        double a = majorAxis();
        double c = focalParameter();
        return std::sqrt(a * a - c * c);
    }

    double perimeter() const override {
        double a = majorAxis();
        double b = minorAxis();
        //NOLINTNEXTLINE
        double X = 3 * (a - b) * (a - b) / (a + b) / (a + b);
        //NOLINTNEXTLINE
        return M_PI * (a + b) * (1 + X / (10 + std::sqrt(4 - X)));
    }

    double area() const override {
        return M_PI * majorAxis() * minorAxis();
    }

    bool operator==(const Shape& that) const override {
        Ellipse const* that_p = dynamic_cast<Ellipse const*>(&that);
        return that_p == nullptr ? false : *this == *that_p;
    }

    bool operator==(const Ellipse& that) const {
        return center() == that.center() && isCongruentTo(that);
    }

    bool isCongruentTo(const Shape& that) const override {
        Ellipse const* that_p = dynamic_cast<Ellipse const*>(&that);
        return that_p == nullptr ? false : isCongruentTo(*that_p);
    }

    bool isCongruentTo(const Ellipse& that) const {
        return doublesEqual(majorAxis(), that.majorAxis()) &&
               doublesEqual(minorAxis(), that.minorAxis());
    }

    bool isSimilarTo(const Shape& that) const override {
        Ellipse const* that_p = dynamic_cast<Ellipse const*>(&that);
        return that_p == nullptr ? false : isSimilarTo(*that_p);
    }

    bool isSimilarTo(const Ellipse& that) const {
        return eccentricity() == that.eccentricity();
    }

    bool containsPoint(const Point& point) const override {
        auto [focus1, focus2] = focuses();
        return pointDistance(focus1, point) + pointDistance(focus2, point) < focal_dist_;
    }

    Ellipse& rotate(const Point& center, double angle) override {
        focus1_ = rotatePoint(focus1_, center, angle);
        focus2_ = rotatePoint(focus2_, center, angle);
        return *this;
    }

    Ellipse& reflect(const Point& center) override {
        focus1_ = reflectPoint(focus1_, center);
        focus2_ = reflectPoint(focus2_, center);
        return *this;
    }

    Ellipse& reflect(const Line& axis) override {
        focus1_ = reflectPointByAxis(focus1_, axis);
        focus2_ = reflectPointByAxis(focus2_, axis);
        return *this;
    }

    Ellipse& scale(const Point& center, double coefficient) override {
        focus1_ = scalePoint(focus1_, center, coefficient);
        focus2_ = scalePoint(focus2_, center, coefficient);
        focal_dist_ *= coefficient;
        return *this;
    }
};

class Circle : public Ellipse {
public:
    double radius() const {
        return majorAxis();
    }
    Circle(Point center, double radius)
    : Ellipse(center, center, 2 * radius) {}
};

class Rectangle : public Polygon {
private:
    static VerticesT calculateRectangleVertices(
            Point point, Point opposite_point, double sides_ratio) {
        if (sides_ratio < 1) {
            sides_ratio = 1 / sides_ratio;
        }
        double angle_between_diagonals = 2 * std::atan(sides_ratio);
        Point main_diagonal_half = (opposite_point - point) / 2;
        Point second_diagonal_half = rotateVector(main_diagonal_half, angle_between_diagonals);
        Point center = calculateSegmentMiddle(opposite_point, point);
        Point intermidiate_point1 = center - second_diagonal_half;
        Point intermidiate_point2 = center + second_diagonal_half;
        return { point, intermidiate_point1, opposite_point, intermidiate_point2 };
    }

public:
    Rectangle(Point point, Point opposite_point, double sides_ratio)
    : Polygon(calculateRectangleVertices(point, opposite_point, sides_ratio)) {}

    Point center() const {
        const VerticesT& vertices = getVertices();
        return calculateSegmentMiddle(vertices[0], vertices[2]);
    }

    std::pair<Line, Line> diagonals() const {
        const VerticesT& vertices = getVertices();
        return { Line(vertices[0], vertices[2]),
        //NOLINTNEXTLINE
                 Line(vertices[1], vertices[3]) };
    }
};
class Square : public Rectangle { public:
    Circle circumscribesCircle() const {
        const auto& vertices = getVertices();
        return { center(), pointDistance(vertices[0], vertices[2]) / 2 };
    }

    Circle inscribedCircle() const {
        const auto& vertices = getVertices();
        return { center(), pointDistance(vertices[0], vertices[1]) / 2 };
    }

    Square(Point point, Point opposite_point)
    : Rectangle(point, opposite_point, 1) {}
};

class Triangle : public Polygon {
public:
    Triangle(Point vertex1, Point vertex2, Point vertex3)
    : Polygon(vertex1, vertex2, vertex3) {}

    Circle circumscribedCircle() const {
        const auto& vertices = getVertices();
        Line middleperpendicular1 = constructMiddleperpendicular(vertices[0], vertices[1]);
        Line middleperpendicular2 = constructMiddleperpendicular(vertices[1], vertices[2]);
        Point circle_center = intersectLines(middleperpendicular1, middleperpendicular2);
        double radius = pointDistance(vertices[0], circle_center);
        return { circle_center, radius };
    }

    Circle inscribedCircle() const {
        const auto& vertices = getVertices();
        double weight0 = pointDistance(vertices[1], vertices[2]);
        double weight1 = pointDistance(vertices[0], vertices[2]);
        double weight2 = pointDistance(vertices[0], vertices[1]);
        double weights_sum = weight0 + weight1 + weight2;
        Point circle_center = (1 / weights_sum) *
            (weight0 * vertices[0] + weight1 * vertices[1] + weight2 * vertices[2]);
        double circle_radius = 2 * area() / perimeter();
        return { circle_center, circle_radius };
    }

    Point centroid() const {
        const auto& vertices = getVertices();
        //NOLINTNEXTLINE
        return std::accumulate(vertices.begin(), vertices.end(), Point(0, 0)) / 3;
    }

    Point orthocenter() const {
        const auto& vertices = getVertices();
        Point o = circumscribedCircle().center();
        Point oa = vertices[0] - o;
        Point ob = vertices[1] - o;
        Point oc = vertices[2] - o;
        return o + oa + ob + oc;
    }

    Line EulerLine() const {
        return { orthocenter(), circumscribedCircle().center() };
    }

    Circle ninePointsCircle() const {
        const auto& vertices = getVertices();
        Point middle1 = calculateSegmentMiddle(vertices[0], vertices[1]);
        Point middle2 = calculateSegmentMiddle(vertices[1], vertices[2]);
        Point middle3 = calculateSegmentMiddle(vertices[2], vertices[0]);
        return Triangle(middle1, middle2, middle3).circumscribedCircle();
    }
};

