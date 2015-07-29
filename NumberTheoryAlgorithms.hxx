#ifndef NUMBERTHEORYALGORITHMS_HXX_INCLUDED
#define NUMBERTHEORYALGORITHMS_HXX_INCLUDED

#include <ostream>
#include <vector>
#include <algorithm>
#include <tuple> // std::tie/make_tuple for parallel assignments

#include <boost/container/static_vector.hpp>

template <typename Range, typename T>
bool contains( Range const& r, T const& v ) {
	using std::begin; using std::end;
	auto e = end(r);
	return std::find(begin(r), e, v) != e;
}

template <typename Range, typename T, typename Pred>
bool contains( Range const& r, T const& v, Pred pred ) {
	using std::begin; using std::end;
	auto e = end(r);
	return std::find_if(begin(r), e, [&] (auto i) {return pred(i, v);}) != e;
}

using u128 = unsigned __int128;
using i128 =          __int128;
using u64 = std::uint64_t;
using i64 = std:: int64_t;
using u32 = std::uint32_t;
using i32 = std:: int32_t;

constexpr u64 operator "" _u64( unsigned long long u ) {return u;}

#define CONCAT_(a, b) a##b
#define CONCAT(a, b) CONCAT_(a,b)
#define K(N) CONCAT_(N,000)
#define M(N) K(K(N))
#define G(N) K(M(N))
#define T(N) M(M(N))
const u64 ten_pow[] {1,    10,    100,
                   K(1), K(10), K(100),
                   M(1), M(10), M(100),
                   G(1), G(10), G(100),
                   T(1), T(10), T(100),
                   T(K(1)), T(K(10)), T(K(100)),
                   T(M(1)), CONCAT(T(M(10)), ull)}; // T(M(10)) = 10^12*10^7 = 10^19
#undef K
#undef M
#undef G
#undef T
#undef CONCAT_

// floored logarithm to base 10 - e.g. ilog10(68'541) = 4
u64 ilog10(u64 i) {
	return std::upper_bound(std::begin(ten_pow)+1, std::end(ten_pow), i) - std::begin(ten_pow) - 1;
}

// Concats the decimal representations of two numbers to produce a third one
u64 concat_dec(u64 a, u64 b) {
	return a*ten_pow[ilog10(b)+1] + b;
}

template <typename U> auto  ceil_mod( U n, U m ) {return n + !!(n%m)*(m - n%m);}
template <typename U> auto floor_mod( U n, U m ) {return n - n%m;}

template <typename U>
U count_multiples(U start, U end, U factor) {
	start = ceil_mod(start, factor);
	return (end-start) / factor + 1;
}
template <typename U>
U sum_multiples(U start, U end, U factor) {
	if (factor > end) return 0;
	start = ceil_mod(start, factor);
	end = floor_mod(end, factor);
	return ((end-start) / factor + 1)*(end+start) / 2;
}

/* Counts/sums the amount of integers x in [start, end]
   s.t. x is either divisible by factor1 or factor2, but not both.
   requires factor1 ⊥ factor2 */

u64 count_xor_multiples( u64 start, u64 end, u64 factor1, u64 factor2) {
	return count_multiples(start, end, factor1) + count_multiples(start, end, factor2)
	     - 2*count_multiples(start, end, factor1*factor2); // Replace by lcm if (factor1, factor2) != 1
}

template <typename U>
U sum_xor_multiples( U start, U end, U factor1, U factor2) {
	return sum_multiples(start, end, factor1) + sum_multiples(start, end, factor2)
	      - 2*sum_multiples(start, end, factor1*factor2);
}


u64 mulmod(u64 a, u64 b, u64 m)
{
	u64 r;
	asm
	( "mulq %2\n\t"
	  "divq %3"
	: "=&d" (r), "+%a" (a)
	: "rm"  (b), "rm"  (m)
	: "cc"
	);
	return r;
}

i64 smulmod(i64 a, i64 b, u64 m)
{
	assert(a >= 0 && b >= 0);
	return mulmod((u64)a, (u64)b, m);
}

u64 mul_inverse( i64 x, i64 m )
{
	i64 t=0, newt = 1;
	i64 r=m, newr = x;

	while (newr)
	{
		auto q = r / newr;
		std::tie(t, newt) = std::make_tuple(newt, t - q*newt);
		std::tie(r, newr) = std::make_tuple(newr, r - q*newr);
	}

	if (r > 1)
		return -1;

	return (t<0) * m + t;
}

u64 sqrmod(u64 t, u64 m)
{
	return mulmod(t, t, m);
}

u64 powmod( u64 x, u64 exp, u64 mod )
{
	u64 res = 1;

	for (; exp; exp >>= 1)
	{
		if (exp&1)
			res = mulmod(res, x, mod);

		x = sqrmod(x, mod);
	}

	return res;
}

u64 binpow( u64 x, u64 exp )
{
	u64 res = 1;

	for (; exp; exp >>= 1)
	{
		if (exp&1)
			res *= x;

		x *= x;
	}

	return res;
}

u64 ipow( u64 b, u32 e )
{
	u64 r = 1;
	while (e--)
		r *= b;

	return r;
}

u64 facmod( u64 n, u64 mod ) {
	const u64 arr[] {
		1, 1, 2, 6, 24, 120, 720, 5'040, 40'320, 362'880, 3'628'800, 39'916'800,
		479'001'600, 6'227'020'800, 87'178'291'200, 1'307'674'368'000, 20'922'789'888'000,
		355'687'428'096'000, 6'402'373'705'728'000, 121'645'100'408'832'000, 2'432'902'008'176'640'000
	};
	auto table_size = sizeof arr / sizeof *arr;

	if (n < table_size)
		return arr[n] % mod;

	u64 prod = arr[table_size-1] % mod;
	n -= table_size-1;
	while (n--)
		prod = mulmod(prod, table_size++, mod);

	return prod;
}

template<typename T>
struct Power
{
	T base;
	unsigned exp : 8;

	Power(T a, uint8_t b) : base{a}, exp{b} {}

	friend std::ostream& operator<<( std::ostream& os, Power p )
	{
		return os << p.base << '^' << p.exp;
	}
};

template<typename T>
auto getFactorization( T N )
{
	std::vector<Power<T>> rval;
	for( T divisor = 2; N != 1; ++divisor )
	{
		std::div_t d = std::div(N, divisor);

		if (d.rem != 0)
		{
			if (divisor >= N/2)
			{
				rval.emplace_back(N, 1);
				break;
			}
			continue;
		}

		rval.emplace_back(divisor, 0);
		N = d.quot;

		for(;;)
		{
			++rval.back().exp;
			d = std::div(N, divisor);
			if (d.rem != 0) break;
			N = d.quot;
		}
	}

	return rval;
}

template<typename T>
T totient( T N )
{
	auto vec = getFactorization(N);
	T tot = 1;
	for( auto p : vec )
		tot *= std::pow( p.base, p.exp-1 ) * (p.base-1);
	return tot;
}

int moebius( u64 N )
{
	if( N == 1 ) return 1;

	unsigned count = 0;

	auto root = std::sqrt(N)+1;
	u64 end = root;

	if( end == root ) return 0;

	for( unsigned div = 2; div != end && N > 1 ; ++div )
		if( N % div == 0 )
		{
			N /= div;
			if( N % div == 0 ) return 0;
			++count;
		}

	if( N > 1 ) ++count;

	return count % 2? -1 : 1;
}

#include <cmath>

template<typename T>
T properDivisorSum( T N )
{
	if (N==1) return 1;

	T sum = 1 + N;
	T i = 2;
	for (; i*i < N; ++i)
		if (N%i == 0)
			sum += i + N/i;

	if (i*i == N)
		sum += i;

	return sum;
}


std::vector<bool> createPrimeTable( std::vector<bool>::size_type max )
{
	std::vector<bool> prime(max, true);
	prime[0] = prime[1] = false;

	for( std::vector<bool>::size_type div = 2;; )
	{
		for( std::vector<bool>::size_type s = 2*div; s < max; s += div )
			prime[s] = false;

		for( std::vector<bool>::size_type next = div;; )
		{
			if( ++next == max/2 ) return prime;
			if( prime[next] ) { div = next; break; }
		}
	}
}

template<typename T>
std::vector<T> createPrimeList( T const max, std::vector<bool> const& table )
{
	std::vector<T> rval;
	for( std::vector<bool>::size_type i = 2; i != max; ++i )
		if( table[i] )
			rval.push_back(i);

	return rval;
}

template<typename T>
std::vector<T> createPrimeList( T const max )
{
	return createPrimeList(max, createPrimeTable(max));
}

template<typename T>
bool isPrime( T N )
{
	T const root = std::sqrt(N)+1;
	for( T div = 2; div < root; ++div )
		if( N % div == 0 ) return false;

	return true;
}

template<std::size_t MaxN, typename Int>
auto primeFactorizations( Int N )
{
	std::vector<boost::container::static_vector<Power<Int>, MaxN>> rval(N);

	auto const primes = createPrimeTable(N);

	for (u64 p = 2; p != primes.size(); ++p)
	if (primes[p])
	{
		for( auto i = p; i < N; i += p )
			rval[i].emplace_back(p, 1);
		unsigned exp = 2;
		for( auto base_pow = p*p; base_pow < N; base_pow *= p, ++exp )
		for( auto i = base_pow; i < N; i += base_pow )
			rval[i].back().exp = exp;
	}

	return rval;
}

template <std::size_t Max, typename Int>
auto divisorCounts( Int N )
{
	std::vector<boost::container::static_vector<uint8_t, Max>> products(N);

	auto const primes = createPrimeTable(N);
	for (std::size_t p = 2; p != primes.size(); ++p)
		if (primes[p])
		{
			for( auto i = p; i < N; i += p )
				products[i].emplace_back(2);
			for( auto base_pow = p*p; base_pow < N; base_pow *= p )
				for( auto i = base_pow; i < N; i += base_pow )
					++products[i].back();
		}

	std::vector<Int> rval; rval.reserve(N);
	for (std::size_t i = 0; i != N; ++i)
		rval.push_back( std::accumulate(std::begin(products[i]), std::end(products[i]), Int(1), std::multiplies<>()) );

	return rval;
}

auto moebiusValues( u64 N )
{
	std::vector<bool> prime(N, true);
	std::vector<int8_t> moebius(N, 1);

	for( u64 div = 2;; )
	{
		auto div_square = div*div;
		moebius[div] = -1;
		for( auto s = 2*div; s < N; s += div )
		{
			prime[s] = false;
			moebius[s] = (s % div_square != 0) * -moebius[s];
		}

		for( auto next = div;; )
		{
			if( ++next == N/2 )
				return moebius;

			if( prime[next] )
			{
				div = next;
				break;
			}
		}
	}
}

auto quadratic_nonresidue(uint32_t p)
{
	for (uint32_t z = 2; z != p; ++z)
		if ( powmod( z, (p-1)/2, p ) != 1 )
			return z;

	assert(false);
}

u64 TonelliShanks( u64 p, u64 a )
{
	u32 s = p - 1;
	auto e = __builtin_ctzll(s);
	s >>= e;

	if (e == 1)
		return powmod( a, p/4 + 1, p );

	u64 n = quadratic_nonresidue(p);

	u64 x = powmod( a, (s+1)/2, p ),
	    b = powmod( a, s, p ),
	    g = powmod( n, s, p ),
	    r = e;

	while (b != 1)
	{
		unsigned m = 1;
		for( u64 b_ = b;; ++m )
		{
			b_ = b_ * b_ % p;

			if( b_ == 1 )
				break;
		}

		for( unsigned index = 0; index != r - m - 1; ++index )
			g = g * g % p;

		x = x * g % p;
		g = g * g % p;
		b = b * g % p;
		r = m;
	}

	return x;
}

std::vector<u32> totients( u64 N )
{
	std::vector<u32> rval(N, 1);

	auto const primes = createPrimeTable(N);

	for (u64 p = 2; p != primes.size(); ++p)
	if (primes[p])
	{
		for( auto i = p; i < N; i += p )
			rval[i] *= p-1;
		for( auto base_pow = p*p; base_pow < N; base_pow *= p )
		for( auto i = base_pow; i < N; i += base_pow )
			rval[i] *= p;
	}

	return rval;
}

i64 faulhaber( u64 n, u64 p, u64 mod )
{
	i64 sum = 0;
	i64 ber_vec[p+1]; // VLA for efficiency

	u64 binom = 1;

	for (u64 j = 0; j <= p; ++j)
	{
		ber_vec[j] = mul_inverse(j+1, mod);
		for (unsigned i = j; i >= 1; --i)
			ber_vec[i-1] = mulmod(i, ber_vec[i-1] + mod - ber_vec[i], mod);

		auto value = mulmod( mulmod(binom, j == 1? mod - ber_vec[0] : ber_vec[0], mod),
		                     powmod(n, p+1-j, mod),
		                     mod );

		if (j % 2 == 0)
			sum += value;
		else
		{
			sum -= value;
			sum += mod;
		}
		sum %= mod;

		// next binominal coefficient:
		binom = mulmod(binom,
		               mulmod(p+1-j,
		                      mul_inverse(j+1, mod),
		                      mod),
		               mod);
	}

	return mulmod(sum, mul_inverse(p+1, mod), mod);
}

template <typename Int, std::size_t MaxN1, std::size_t MaxN2, std::size_t zippedMaxN = MaxN1+MaxN2>
boost::container::static_vector<Power<Int>, zippedMaxN>
zipFactors( boost::container::static_vector<Power<Int>, MaxN1> const& lhs,
            boost::container::static_vector<Power<Int>, MaxN2> const& rhs )
{
	boost::container::static_vector<Power<Int>, zippedMaxN> rval(std::begin(lhs), std::end(lhs));
	for (auto&& pow : rhs)
	{
		auto iter = std::find_if( std::begin(rval), std::end(rval), [base = pow.base] (auto& p) {return p.base == base;} );
		if (iter != std::end(rval))
			iter->exp += pow.exp;
		else
			rval.push_back( pow );
	}

	return rval;
}

template <std::size_t index>
struct enumerateDivisors
{
	template <typename Func,
	          typename InputIterator>
	static void call( u64 Cap,
	                  u64 current,
	                  InputIterator pows,
	                  Func f )
	{
		for (int i = 0; current < Cap && i <= pows->exp; ++i)
		{
			enumerateDivisors<index-1>::call(Cap, current, std::next(pows), f);
			current *= pows->base;
		}
	}
};

template <>
template <typename Func,
          typename InputIterator>
void enumerateDivisors<0>::call( u64 Cap,
                  u64 current,
                  InputIterator pows,
                  Func f )
{
	for (int i = 0; current < Cap && i <= pows->exp; ++i)
	{
		f(current);
		current *= pows->base;
	}
}

template <typename Iter, typename Func>
void foreachDivisor( Iter first, Iter last, Func f, u64 Cap )
{
	static constexpr decltype(&enumerateDivisors<0>::call<Func, Iter>) arr[]
	{
		enumerateDivisors<0 >::call<Func, Iter>,
		enumerateDivisors<1 >::call<Func, Iter>,
		enumerateDivisors<2 >::call<Func, Iter>,
		enumerateDivisors<3 >::call<Func, Iter>,
		enumerateDivisors<4 >::call<Func, Iter>,
		enumerateDivisors<5 >::call<Func, Iter>,
		enumerateDivisors<6 >::call<Func, Iter>,
		enumerateDivisors<7 >::call<Func, Iter>,
		enumerateDivisors<8 >::call<Func, Iter>,
		enumerateDivisors<9 >::call<Func, Iter>,
		enumerateDivisors<10>::call<Func, Iter>,
		enumerateDivisors<11>::call<Func, Iter>,
		enumerateDivisors<12>::call<Func, Iter>,
		enumerateDivisors<13>::call<Func, Iter>,
		enumerateDivisors<14>::call<Func, Iter>,
		enumerateDivisors<15>::call<Func, Iter>
	};

	if (std::size_t diff = std::distance(first, last))
	{
		assert(diff < sizeof arr / sizeof *arr);
		arr[diff-1]( Cap, 1, first, f );
	}
}


template <std::size_t index>
struct enumerateCombinations
{
	template <typename Func,
	          typename InputIterator>
	static void call( Func f, InputIterator bases, u64 Cap, u64 min_distinct, u64 current=1, u64 distinct=0 )
	{
		auto next_p = std::next(bases);
		auto p = *bases;
		if (current < Cap) {
				enumerateCombinations<index-1>::call(f, next_p, Cap, min_distinct, current, distinct);
			while ((current *= p) < Cap)
				enumerateCombinations<index-1>::call(f, next_p, Cap, min_distinct, current, distinct+1);
		}
	}
};

template <>
template <typename Func,
          typename InputIterator>
void enumerateCombinations<0>::call( Func f, InputIterator bases, u64 Cap, u64 min_distinct, u64 current, u64 distinct )
{
	if (distinct+1 == min_distinct)
		current *= *bases;
	else if (distinct < min_distinct)
		return;
	while (current < Cap)
	{
		f(current);
		current *= *bases;
	}
}

/* For all primes in [first, last), call f with all products of powers of these primes that don't
   exceed Cap but have at least min_distinct distinct prime factors */
template <typename ForwardIt, typename Func>
void foreachCombination( ForwardIt first, ForwardIt last, Func f, u64 Cap, u64 min_distinct )
{
	static constexpr decltype(&enumerateCombinations<0>::call<Func, ForwardIt>) arr[]
	{
		enumerateCombinations<0 >::call<Func, ForwardIt>,
		enumerateCombinations<1 >::call<Func, ForwardIt>,
		enumerateCombinations<2 >::call<Func, ForwardIt>,
		enumerateCombinations<3 >::call<Func, ForwardIt>,
		enumerateCombinations<4 >::call<Func, ForwardIt>,
		enumerateCombinations<5 >::call<Func, ForwardIt>,
		enumerateCombinations<6 >::call<Func, ForwardIt>,
		enumerateCombinations<7 >::call<Func, ForwardIt>,
		enumerateCombinations<8 >::call<Func, ForwardIt>,
		enumerateCombinations<9 >::call<Func, ForwardIt>,
		enumerateCombinations<10>::call<Func, ForwardIt>,
		enumerateCombinations<11>::call<Func, ForwardIt>,
		enumerateCombinations<12>::call<Func, ForwardIt>,
		enumerateCombinations<13>::call<Func, ForwardIt>,
		enumerateCombinations<14>::call<Func, ForwardIt>,
		enumerateCombinations<15>::call<Func, ForwardIt>
	};

	if (std::size_t diff = std::distance(first, last))
	{
		assert(diff < sizeof arr / sizeof *arr);
		arr[diff-1]( Cap, min_distinct, 1, first, f );
	}
}

template <typename T>
T square(T t) {return t*t;}

namespace detail
{
	bool witnessTest(u32 s, u64 N, u64 d, u64 a)
	{
		auto x = powmod(a, d, N);
		u64 y;

		while (s-- != 0) {
			y = sqrmod(x, N);
			if (y == 1 && x != 1 && x != N-1)
				return false;
			x = y;
		}

		return y == 1;
	}
}

bool deterministicMillerRabin(u64 N)
{
	if ((N%2 == 0 && N != 2) || (N < 2) || (N % 3 == 0 && N != 3)) return false;
	if (N <= 3) return true;
	auto d = N-1;
	u32 s = 0;
	while (d%2 == 0) {
		++s;
		d /= 2;
	}

	using namespace detail;

	auto check = [=] (auto... args) {for(auto i : {args...}) if (!witnessTest(s, N, d, i)) return false; return true; };

	if (N < 2047      )    return check(2);
	if (N < 1373653   )    return check(2, 3);
	if (N < 9080191   )    return check(                        31,     73);
	if (N < 4759123141)    return check(2,       7,                 61);
	if (N < 1122004669633) return check(2,              13, 23,            1662803);
	if (N < 2152302898747) return check(2, 3, 5, 7, 11);
	if (N < 3474749660383) return check(2, 3, 5, 7, 11, 13);

	return check(2, 3, 5, 7, 11, 13, 17);
}

// Useful for inverse totient trees and such
template <typename OutputIt>
void findInvTotPrimes( u64 n, OutputIt out ) {
	for (u64 d=1; d*d <= n; ++d)
		if (n%d == 0) {
			if (deterministicMillerRabin(d+1))
				*out++ = d+1;
			if (deterministicMillerRabin(n/d+1) && __builtin_expect(n/d != d, true))
				*out++ = n/d+1;
		}
}

#endif // NUMBERTHEORYALGORITHMS_HXX_INCLUDED
