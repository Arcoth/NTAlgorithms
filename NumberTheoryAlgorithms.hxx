#ifndef NUMBERTHEORYALGORITHMS_HXX_INCLUDED
#define NUMBERTHEORYALGORITHMS_HXX_INCLUDED

#include <ostream>
#include <vector>
#include <algorithm>
#include <tuple> // std::tie/make_tuple for parallel assignments

#include <boost/container/static_vector.hpp>

uint64_t mulmod(uint64_t a, uint64_t b, uint64_t m)
{
	uint64_t r;
	asm
	( "mulq %2\n\t"
	  "divq %3"
	: "=&d" (r), "+%a" (a)
	: "rm"  (b), "rm"  (m)
	: "cc"
	);
	return r;
}

int64_t smulmod(int64_t a, int64_t b, uint64_t m)
{
	assert(a >= 0 && b >= 0);
	return mulmod((uint64_t)a, (uint64_t)b, m);
}

int64_t mul_inverse( int64_t x, int64_t m )
{
	int64_t t=0, newt = 1;
	int64_t r=m, newr = x;

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

uint64_t mulsqr(uint64_t t, uint64_t m)
{
	return mulmod(t, t, m);
}

uint64_t powmod( uint64_t x, uint64_t exp, uint64_t const mod )
{
	uint64_t res = 1;

	for (; exp; exp >>= 1)
	{
		if (exp&1)
			res = mulmod(res, x, mod);

		x = mulsqr(x, mod);
	}

	return res;
}

uint64_t binpow( uint64_t x, uint64_t exp )
{
	uint64_t res = 1;

	for (; exp; exp >>= 1)
	{
		if (exp&1)
			res *= x;

		x *= x;
	}

	return res;
}

uint64_t ipow( uint64_t b, uint32_t e )
{
	uint64_t r = 1;
	while (e--)
		r *= b;

	return r;
}

template<typename Container>
bool contains( Container const& c, typename Container::value_type const& to_find )
{
	auto end = std::end(c);
	return std::find( std::begin(c), end, to_find ) != end;
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

int moebius( uint64_t N )
{
	if( N == 1 ) return 1;

	unsigned count = 0;

	auto root = std::sqrt(N)+1;
	uint64_t end = root;

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
	T sum = 1 + N;
	auto const root = std::sqrt(N);
	T end = root;
	for( T i = 2; i != end; ++i )
		if( N % i == 0 )
			sum += i + N/i;

	if( end == root )
		sum += end;

	return sum;
}


std::vector<bool> createPrimeTable( std::vector<bool>::size_type max )
{
	std::vector<bool> prime(max, true);

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

	for (std::uint64_t p = 2; p != primes.size(); ++p)
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

auto moebiusValues( uint64_t N )
{
	std::vector<bool> prime(N, true);
	std::vector<int8_t> moebius(N, 1);

	for( uint64_t div = 2;; )
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

uint64_t TonelliShanks( unsigned p, unsigned a )
{
	auto s = p - 1;
	unsigned e = __builtin_ctz(s);
	s >>= e;

	if( e == 1 )
		return powmod( a, p/4 + 1, p );

	uint64_t n = quadratic_nonresidue(p);

	uint64_t x = powmod( a, (s+1)/2, p ),
	         b = powmod( a, s, p ),
	         g = powmod( n, s, p ),
	         r = e;

	while( b != 1 )
	{
		unsigned m = 1;
		for( uint64_t b_ = b;; ++m )
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

std::vector<uint64_t> totients( uint64_t N )
{
	std::vector<uint64_t> rval;
	rval.reserve(N);
	for( auto const& prime_powers : primeFactorizations<9>(N) )
	{
		uint64_t product = 1;
		for( auto p : prime_powers )
			product *= ipow(p.base, p.exp-1) * (p.base - 1);
		rval.emplace_back(product);
	}

	return rval;
}

int64_t faulhaber( uint64_t n, uint64_t p, uint64_t mod )
{
	int64_t sum = 0;
	int64_t ber_vec[p+1]; // VLA for efficiency

	uint64_t binom = 1;

	for (uint64_t j = 0; j <= p; ++j)
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
	static void call( std::uint64_t Cap,
	                  std::uint64_t current,
	                  InputIterator pows,
	                  Func f ) __attribute__((always_inline))
	{
		for (int i = 0; current < Cap && i <= pows->exp; ++i)
		{
			enumerateDivisors<index-1>::call(Cap, current, std::next(pows), f);
			current *= pows->base;
		}
	}
};

template <>
struct enumerateDivisors<0>
{
	template <typename Func,
	          typename InputIterator>
	static void call( std::uint64_t Cap,
	                  std::uint64_t current,
	                  InputIterator pows,
	                  Func f ) __attribute__((always_inline))
	{
		for (int i = 0; current < Cap && i <= pows->exp; ++i)
		{
			f(current);
			current *= pows->base;
		}
	}
};

template <typename Iter, typename Func>
void foreachDivisor( Iter first, Iter last, Func f, std::uint64_t Cap )
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

#endif // NUMBERTHEORYALGORITHMS_HXX_INCLUDED
