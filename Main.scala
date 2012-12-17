import annotation.tailrec

object Part1 {

  case class State[S,+A](runS: S => (A,S)) {
    def map[B](f: A => B) =
      State[S, B](s => {
        val (a,s1) = runS(s)
        (f(a),s1)
      })
    def flatMap[B](f: A => State[S,B]) =
      State[S,B](s => {
        val (a,s1) = runS(s)
        f(a) runS s1
      })
  }

  def getState[S]: State[S,S] =
    State(s => (s,s))

  def setState[S](s: S): State[S,Unit] =
    State(_ => ((),s))

  def pureState[S, A](a: A): State[S, A] =
    State(s => (a,s))

  def zipIndex[A](as: List[A]): List[(Int,A)] =
    as.foldLeft(
      pureState[Int, List[(Int,A)]](List())
    )((acc,a) => for {
      xs <- acc
      n  <- getState
      _  <- setState(n + 1)
    } yield (n,a)::xs).runS(0)._1.reverse
}

object Part2 {
  @tailrec def foldl[A,B](as: List[A], b: B,
                 f: (B,A) => B): B =
    as match {
      case Nil => b
      case x :: xs => foldl(xs, f(b,x), f)
    }

  def foldl2[A,B](as: List[A], b: B,
                 f: (B,A) => B): B = {
    var z = b
    var az = as
    while (true) {
      az match {
        case Nil => return z
        case x :: xs => {
          z = f(z, x)
          az = xs
        }
      }
    }
    z
  }

  def even[A](ns: List[A]): Boolean =
    ns match {
      case Nil => true
      case x :: xs => odd(xs)
    }

  def odd[A](ns: List[A]): Boolean =
    ns match {
      case Nil => false
      case x :: xs => even(xs)
    }
}

object Part3 {
  sealed trait Trampoline[+A] {
    final def runT: A =
      this match {
        case More(k) => k().runT
        case Done(v) => v
      }
  }

  case class More[+A](k: () => Trampoline[A])
    extends Trampoline[A]

  case class Done[+A](result: A)
    extends Trampoline[A]

  def even[A](ns: List[A]): Trampoline[Boolean] =
    ns match {
      case Nil => Done(true)
      case x :: xs => More(() => odd(xs))
    }

  def odd[A](ns: List[A]): Trampoline[Boolean] =
    ns match {
      case Nil => Done(false)
      case x :: xs => More(() => even(xs))
    }
}

object Parts4And5 {

  case class State[S,+A](runS: S => Trampoline[(A,S)]) {
    def map[B](f: A => B) =
      State[S, B](s => {
        runS(s) map { case (a,s1) => (f(a), s1) }
      })
    def flatMap[B](f: A => State[S,B]) =
      State[S,B](s => More(() => runS(s) flatMap {
        case (a,s1) => More(() => f(a) runS s1)
      }))
  }

  def getState[S]: State[S,S] =
    State(s => (s,s))

  def setState[S](s: S): State[S,Unit] =
    State(_ => ((),s))

  def pureState[S, A](a: A): State[S, A] =
    State(s => (a,s))

  sealed trait Trampoline[+A] {
    def map[B](f: A => B): Trampoline[B] =
      flatMap(x => More(() => Done(f(x))))
    def flatMap[B](f: A => Trampoline[B]): Trampoline[B] =
      this match {
        case FlatMap(a, g) =>
          FlatMap(a, (x: Any) => g(x) flatMap f)
        case x => FlatMap(() => x, f)
      }
    @tailrec final def resume: Either[() => Trampoline[A], A] =
      this match {
        case Done(v) => Right(v)
        case More(k) => Left(k)
        case FlatMap(a, f) => a() match {
          case Done(v) => f(v).resume
          case More(k) => Left(() => k() flatMap f)
          case b FlatMap g => b().flatMap((x:Any) => g(x) flatMap f).resume
        }
    }
    @tailrec final def runT: A = resume match {
      case Right(a) => a
      case Left(k) => k().runT
    }
    def zip[B](b: Trampoline[B]): Trampoline[(A,B)] =
      (this.resume, b.resume) match {
        case (Right(a), Right(b)) => Done((a, b))
        case (Left(a), Left(b)) => More(() => a() zip b())
        case (Left(a), Right(b)) => More(() => a() zip Done(b))
        case (Right(a), Left(b)) => More(() => Done(a) zip b())
      }
  }
  case class More[A](k: () => Trampoline[A]) extends Trampoline[A]
  case class Done[A](result: A) extends Trampoline[A]
  case class FlatMap[A,B](a: () => Trampoline[A], f: A => Trampoline[B]) extends Trampoline[B]

  def zipIndex[A](as: List[A]): List[(Int,A)] =
    as.foldLeft(
      pureState[Int, List[(Int,A)]](List())
    )((acc,a) => for {
      xs <- acc
      n <- getState
      _ <- setState(n + 1)
    } yield n -> a :: xs).runS(0).runT._1.reverse

  implicit def step[A](a: => A): Trampoline[A] =
    More(() => Done(a))

  def fib(n: Int): Trampoline[Int] =
    if (n <= 1) Done(n) else for {
      x <- More(() => fib(n-1))
      y <- More(() => fib(n-2))
    } yield x + y

}

object Part6 {

  sealed trait Free[S[+_],+A] {
    private case class FlatMap[S[+_],A,+B](a: () => Free[S,A],f: A => Free[S,B]) extends Free[S,B]

    def map[B](f: A => B): Free[S,B] =
      flatMap(x => Done(f(x)))

    def flatMap[B](f: A => Free[S,B]): Free[S,B] =
      this match {
        case FlatMap(a, g) =>
          FlatMap(a, (x: Any) => g(x) flatMap f)
        case x => FlatMap(() => x, f)
      }

    @tailrec final def resume(implicit S: Functor[S]): Either[S[Free[S, A]], A] =
      this match {
        case Done(a)  => Right(a)
        case More(k) => Left(k)
        case a FlatMap f  => a() match {
          case Done(a)  => f(a).resume
          case More(k) => Left(S.map(k)(_ flatMap f))
          case b FlatMap g  => b().flatMap((x: Any) =>
            g(x) flatMap f).resume
        }
      }

    def zip[B](b: Free[S,B])(
      implicit S: Functor[S]): Free[S, (A,B)] =
      (resume, b.resume) match {
        case (Left(a), Left(b)) =>
          More(S.map(a)(x => More(S.map(b)(y => x zip y))))
        case (Left(a), Right(b)) =>
          More(S.map(a)(x => x zip Done(b)))
        case (Right(a), Left(b)) =>
          More(S.map(b)(y => Done(a) zip y))
        case (Right(a), Right(b)) =>
          Done((a, b))
      }
  }

  case class Done[S[+_],+A](a: A) extends Free[S,A]
  case class More[S[+_],+A](k: S[Free[S,A]]) extends Free[S,A]

  type Trampoline[+A] = Free[Function0, A]

  trait Functor[F[_]] {
    def map[A,B](m: F[A])(f: A => B): F[B]
  }

  implicit val f0Functor = new Functor[Function0] {
    def map[A,B](a: () => A)(f: A => B) = () => f(a())
  }

  type Pair[+A] = (A,A)
  type BinTree[+A] = Free[Pair, A]
  type Tree[+A] = Free[List, A]

  type FreeMonoid[A] = Free[({type λ[+α] = (A, α)})#λ, Unit]

  sealed trait StateF[S,+A]
  case class Get[S,A](f: S => A) extends StateF[S,A]
  case class Put[S,A](s: S, a: A) extends StateF[S,A]

  implicit def statefFun[S] = new Functor[({type λ[+α] = StateF[S,α]})#λ] {
    def map[A,B](m: StateF[S, A])(f: A => B) = m match {
      case Get(g) => Get((s:S) => f(g(s)))
      case Put(s, a) => Put(s, f(a))
    }
  }

  type FreeState[S,+A] = Free[({type λ[+α] = StateF[S,α]})#λ, A]

  def pureState[S,A](a: A): FreeState[S,A] = Done[({type λ[+α] = StateF[S,α]})#λ, A](a)
  def getState[S]: FreeState[S,S] = More[({type λ[+α] = StateF[S,α]})#λ, S](Get(s =>
  Done[({type λ[+α] = StateF[S,α]})#λ, S](s)))
  def setState[S](s: S): FreeState[S,Unit] = More[({type λ[+α] = StateF[S,α]})#λ, Unit](Put(s,
  Done[({type λ[+α] = StateF[S,α]})#λ, Unit](())))

  def evalS[S,A](s: S, t: FreeState[S,A]): A = t.resume match {
    case Left(Get(f)) => evalS(s, f(s))
    case Left(Put(n, a)) => evalS(n, a)
    case Right(a) => a
  }

}

