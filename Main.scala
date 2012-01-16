sealed trait Trampoline[+A] {
  def map[B](f: A => B): Trampoline[B] = flatMap(x => More(() => Done(f(x))))
  def flatMap[B](
    f: A => Trampoline[B]): Trampoline[B] =
    this match {
      case FlatMap(a, g) =>
        FlatMap(a, (x: Any) => g(x) flatMap f)
      case x => FlatMap(x, f)
    }
  @annotation.tailrec final def resume:
    Either[() => Trampoline[A], A] =
    this match {
      case Done(v) => Right(v)
      case More(k) => Left(k)
      case FlatMap(a,f) => a match {
        case Done(v) => f(v).resume
        case More(k) => Left(() =>
          k() flatMap f)
        case FlatMap(b,g) => (FlatMap(b,
            (x:Any) => g(x) flatMap f
          ):Trampoline[A]).resume
      }
  }
  @annotation.tailrec final def runT: A = resume match {
    case Right(a) => a
    case Left(k) => k().runT 
  }  
def zip[B](b: Trampoline[B]): Trampoline[(A,B)] =
  (this.resume, b.resume) match {
    case (Right(a), Right(b)) =>
      Done((a, b))
    case (Left(a), Left(b)) =>
      More(() => a() zip b())
    case (Left(a), Right(b)) =>
      More(() => a() zip Done(b))
    case (Right(a), Left(b)) =>
      More(() => Done(a) zip b())
  }  
}
case class More[A](k: () => Trampoline[A])
  extends Trampoline[A]
case class Done[A](result: A)
  extends Trampoline[A]
case class FlatMap[A,B](a: Trampoline[A], f: A => Trampoline[B]) extends Trampoline[B]

case class State[S,A](
  runS: S => Trampoline[(A,S)]) {
  def map[B](f: A => B) =
    State[S,B](s => runS(s) map {
      case (a, s1) => f(a) -> s1
    })
  def flatMap[B](f: A => State[S,B]) =
    State[S,B](s => More(() => runS(s) flatMap {
      case (a,s1) => More(() => f(a).runS(s1))
    }))
}

def pure[S,A](a: A) = State[S,A](s => Done(a -> s))
def getState[S] = State[S,S](s => Done(s -> s))
def setState[S,A](s: S) = State[S,Unit](_ => Done(() -> s))

def zipIndex[A](as: List[A]): List[(Int,A)] =                            
  as.foldLeft(
    pure[Int, List[(Int,A)]](List())
  )((acc,a) => for {          
    xs <- acc                                                               
    n  <- getState                                                 
    _  <- setState(n + 1)                                          
  } yield n -> a :: xs).runS(0).runT._1.reverse  


sealed trait Free[S[+_],+A] {
case class Done[S[+_],+A](a: A)
  extends Free[S,A]
case class More[S[+_],+A](
  k: S[Free[S,A]]) extends Free[S,A]
private case class FlatMap[S[+_],A,+B](
  a: Free[S,A],
  f: A => Free[S,B]) extends Free[S,B]
  def map[B](f: A => B): Free[S,B] =
    flatMap(x => Done(f(x)))
  def flatMap[B](
    f: A => Free[S,B]): Free[S,B] =
    this match {
      case FlatMap(a, g) =>
        FlatMap(a, (x: Any) => g(x) flatMap f)
      case x => FlatMap(x, f)
    }

@annotation.tailrec final def resume(implicit S: Functor[S]):
  Either[S[Free[S,A]], A] = this match {
  case Done(a) => Right(a)
  case More(k) => Left(k)
  case FlatMap(a, f)  => a match {
    case Done(a) => f(a).resume
    case More(k) =>
      Left(S.map((x: Free[S,Any]) =>
        x flatMap f)(k))
    case FlatMap(b, g) =>
      (FlatMap(b, (x: Any) =>
        g(x) flatMap f): Free[S,A]).resume
  }
}
def zip[B](b: Free[S,B])(
  implicit S: Functor[S]): Free[S, (A,B)] =
  (resume, b.resume) match {
    case (Left(a), Left(b)) =>
      More(S.map(
        (x: Free[S, A]) => More(S.map(
        (y: Free[S, B]) => x zip y)(b)))(a))
    case (Left(a), Right(b))  =>
      More(S.map(
        (x: Free[S, A]) => x zip Done(b))(a))
    case (Right(a), Left(b)) =>
      More(S.map(
        (y: Free[S, B]) => Done(a) zip y)(b))
    case (Right(a), Right(b)) =>
      Done((a, b))
  }
    

}

