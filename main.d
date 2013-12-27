import std.stdio;
import std.typecons;
import std.math;


int main(string[] args)
{
    auto fout = File("data.txt", "w");
    real r0 = 1.0, v0 = 0.0;
    real m = 1, k = 1, b = 1;
    real t = 0.0, dt = 0.1;
    foreach(i; 0..10)
    {
        fout.writefln("%s %s %s %s", i, t, r0, v0);
        auto newRV = solverRK4(0.1, r0, v0, (t, r, v) {
            return (-k * r - b * v) / m;
        });
        t += dt;
        r0 = newRV[0];
        v0 = newRV[1];
    }
    return 0;
}

auto solverRK4(real dt, real r0, real v0, real delegate(real t, real r, real v) f)
{
    auto k1 = f(0.0, r0, v0) * dt;
    auto q1 = v0 * dt;
    //
    auto k2 = f(dt / 2.0, r0 + q1 / 2.0, v0 + k1 / 2.0) * dt;
    auto q2 = (v0 + k1 / 2.0) * dt;
    //
    auto k3 = f(dt / 2.0, r0 + q2 / 2.0, v0 + k2 / 2.0) * dt;
    auto q3 = (v0 + k2 / 2.0) * dt;
    //
    auto k4 = f(dt, r0 + q3, v0 + k3) * dt;
    auto q4 = (v0 + k3) * dt;
    return tuple(v0 + (k1 + 2.0 * k2 + 2.0 * k3 + k4) / 6.0, v0 + (q1 + 2.0 * q2 + 2.0 * q3 + q4) / 6.0);
}

auto solverRosenbrokExJ(real dt, real r0, real v0, real delegate(real t, real r, real v) f,
                        real delegate(real t, real r, real v) f_r,
                        real delegate(real t, real r, real v) f_v)
{
    real[][] J = [[0.0L, 1.0L], [f_r(0.0L, r0, v0), f_v(0.0L, r0, v0)]];
    return tuple(r0, v0);
}

struct Matrix
{
    public:
        real[][] m;

        this(real[][] original)
        {
            m.length = original.length;

            for(auto i = 0; i < original.length; ++i)
                m[i] = original[i].dup;
        }

        this(this)
        {
            writeln("postblit ctor");
            m = m.dup;
            for(auto i = 0; i < m.length; ++i)
                m[i] = m[i].dup;
        }

        auto opBinary(string op)(Matrix B)
            if(op == "+" || op == "-")
        in
        {
            alias this A;
            assert(A.m.length == B.m.length, "non equal row matrices in operator "~op);
            foreach(i; 0..A.m.length)
            assert(A.m[i].length == B.m[i].length, "non equal column matrices in operator "~op);
        }
        body
        {
            alias this A;
            Matrix C;
            C.m.length = A.m.length;

            for(auto i = 0; i < A.m.length; ++i)
                C.m[i] = A.m[i].dup;

            for(auto i = 0; i < B.m.length; ++i)
                mixin("C.m[i][]"~op~"=B.m[i][];");

            return C;
        }

        auto opBinary(string op)(Matrix B)
            if(op == "*")
        in
        {
            alias this A;
            assert(A.m.length == B.m.length, "non equal row matrices in operator "~op);
            foreach(i; 0..A.m.length)
                assert(A.m[i].length == B.m[i].length, "non equal column matrices in operator "~op);
        }
        body
        {
            alias this A;
            Matrix C;
            C.m.length = A.m.length;

            for(auto i = 0; i < B.m.length; ++i)
            {
                C.m[i].length = B.m[i].length;
                foreach(ref e; C.m[i])
                    e = 0.0L;
            }

            for(auto i = 0; A.m.length; ++i)
                for(auto j = 0; B.m[i].length; ++j)
                    for(auto k = 0; A.m[i].length; ++k)
                        C.m[i][j] += A.m[i][j] * B.m[i][j];

            return C;
        }
}

real[] solveSLAE( Matrix matrix, const real[] vector)
{
    writeln("before copy");
    Matrix M = matrix;
    writeln("after copy");

    for(auto i = 0 ; i < M.m.length; ++i)
        M.m[i] ~= vector[i];

    writeln(M.m);
    writeln(matrix.m);

    void maximizeDiagonal(Matrix M, size_t currentIndex)
    {
        auto max = abs(M.m[currentIndex][currentIndex]);
        auto maxIndex = currentIndex;

        for(auto i = currentIndex; i < M.m.length; ++i)
            if(abs(M.m[i][currentIndex]) > max)
            {
                max = abs(M.m[i][currentIndex]);
                maxIndex = i;
            }

        if(maxIndex != currentIndex)
        {
            auto temp = M.m[currentIndex];
            M.m[currentIndex] = M.m[maxIndex];
            M.m[maxIndex] = temp;
        }
    }


    void forwardGauss(Matrix M)
    {
        for(auto i = 0; i < M.m.length; ++i)
        {
            maximizeDiagonal(M, i);

            if(abs(M.m[i][i]) < sqrt(real.epsilon))
                return;

            for(auto j = i + 1; j < M.m.length; ++j)
            {
                for(auto k = i + 1; k < M.m[j].length; ++k)
                    M.m[j][k] -= (M.m[j][i] / M.m[i][i]) * M.m[i][k];
                M.m[j][i] = 0.0L;
            }
        }
    }


    real[] backwardGauss(Matrix M)
    {
        auto i = M.m.length;
        while(i && abs(M.m[i - 1][i - 1]) < sqrt(real.epsilon))
            if(abs(M.m[i - 1][$ - 1]) < sqrt(real.epsilon))
            {
                M.m[i - 1][$ - 1] = 1.0L;
                --i;
            }
            else
            {
                return new real[M.m.length];
            }

        for(auto j = i;j > 0; --j)
        {
            for(auto k = j; k < M.m[j - 1].length - 1; ++k)
                M.m[j - 1][$ - 1] -= M.m[j - 1][k] * M.m[k][$ - 1];
            M.m[j - 1][$-1]  /= M.m[j - 1][j - 1];
        }
        real[] result= new real[M.m.length];
        for(auto j = 0; j < result.length; ++j)
            result[j] = M.m[j][$ -1];
        return result;
    }
    forwardGauss(M);
    writeln("treug ",M.m);
    return backwardGauss(M);
}

unittest
{
    /*
    Matrix A=[[1.0L, 1, 1, 1], [-3.0L, 2, 2, 2], [2.0L, 3, 3, 3]];
    maximizeDiagonal(A, 0);
    assert(Matrix([[-3.0L, 2, 2, 2], [1.0L, 1, 1, 1], [2.0L, 3, 3, 3]])==A);
    maximizeDiagonal(A, 1);
    assert(Matrix([[-3.0L, 2, 2, 2], [2.0L, 3, 3, 3], [1.0L, 1, 1, 1]])==A);
    maximizeDiagonal(A,2);
    assert(Matrix([[-3.0L, 2, 2, 2], [2.0L, 3, 3, 3], [1.0L, 1, 1, 1]])==A);
    */
    auto norm(real[] vec)
    {
        auto result = 0.0L;
        foreach(e;vec)
            result+=e*e;
        return sqrt(result);
    }

    auto minus(real[] a, real[] b)
    {
        assert(a.length == b.length);
        auto result = a.dup;
        result[] -= b[];
        return result;
    }
    Matrix A=[[1.0L, 0], [0.0L, 1]];
    writeln(A.m);
    assert([2.0L, 3.0L] == solveSLAE(A,[2.0L,3.0L]));
    writeln(A.m);
    Matrix B=[[1.0L, 2], [3.0L, 4]];
    //assert(norm(minus([2.0L, 3.0L], solveSLAE(B, [8.0L, 18.0L]))) < sqrt(real.epsilon));
    writeln(B.m);
    Matrix C=[[1.0L, 2], [2.0L, 4]];
    writeln("solution ", solveSLAE(C, [8.0L, 16.0L]));
    //assert(norm(minus([6.0L, 1.0L], solveSLAE(C, [8.0L, 16.0L]))) < sqrt(real.epsilon));
}

unittest
{
    Matrix A = [[1.0L, 2.0L], [3.0L, 4.0L]];
    Matrix B = [[-1.0L, 3.0L], [3.0L, 4.0L]];
    assert(Matrix([[0.0L, 5.0L], [6.0L, 8.0L]]) == A.opBinary!"+"(B), "operator + in form opBinary!\"+\"(A,B) failed");
    assert(Matrix([[0.0L, 5.0L], [6.0L, 8.0L]]) == A + B, "operator + in form A+B failed");
    assert(Matrix([[2.0L, -1.0L], [0.0L, 0.0L]]) == A.opBinary!"-"(B), "operator - in form opBinary!\"-\"(A,B) failed");
    assert(Matrix([[2.0L, -1.0L], [0.0L, 0.0L]]) == A - B, "operator - in form A-B failed");
}
