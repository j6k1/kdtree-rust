use std::borrow::Borrow;
use std::cell::RefCell;
use std::marker::PhantomData;
use std::ops::{Add, Deref, Mul, Neg, Sub};
use std::rc::Rc;

#[derive(Debug,Clone,Copy,PartialEq,Eq)]
pub enum Color {
    Red,
    Black
}
#[derive(Debug,Clone,Copy,PartialEq,Eq)]
pub enum LR {
    L,
    R
}
#[derive(Debug,Clone,Copy,PartialEq,Eq)]
pub enum Balance {
    Pre,
    Fix,
    None
}
impl Neg for Color {
    type Output = Color;
    fn neg(self) -> Self::Output {
        match self {
            Color::Red => Color::Black,
            Color::Black => Color::Red
        }
    }
}
pub trait EuclideanDistance<T> {
    type Output;
    fn euclidean_distance(&self, rhs:T) -> Self::Output;
}
impl<'a,const D:usize,P> EuclideanDistance<&'a [P;D]> for &'a [P;D]
    where P: PartialOrd + Mul<P, Output = P> + Add<P, Output = P> + Sub<P, Output = P> +
             Clone + Copy + Default + Distance<P, Output = P> {
    type Output = P;

    fn euclidean_distance(&self, rhs: &'a [P; D]) -> P {
        self.iter().zip(rhs.iter()).fold(P::default(),|acc,(p1,p2)| {
            acc + p1.distance(p2)
        })
    }
}
pub trait Distance<T> {
    type Output;

    fn distance(&self, rhs:&T) -> Self::Output;
}
impl<P> Distance<P> for P
    where P: PartialOrd + Mul<P, Output = P> + Add<P, Output = P> + Sub<P, Output = P> +
             Clone + Copy + Default {
    type Output = P;

    fn distance(&self, rhs: &P) -> P {
        if self.partial_cmp(rhs).unwrap().is_le() {
            *rhs - *self
        } else {
            *self - *rhs
        }
    }
}
#[derive(Debug)]
pub struct KDNode<'a,const K:usize,P,T>
    where P: PartialOrd + Mul + Add + Sub +
             Clone + Copy + Default + Distance<P, Output = P> + 'a,
             &'a [P; K]: EuclideanDistance<&'a [P; K], Output = P> + 'a {
    positions:Rc<[P; K]>,
    value:Rc<RefCell<T>>,
    color: Rc<RefCell<Color>>,
    left:Option<Box<KDNode<'a, K,P,T>>>,
    right:Option<Box<KDNode<'a, K,P,T>>>,
    l:PhantomData<&'a ()>
}
impl<'a,const K:usize,P,T> KDNode<'a, K,P,T>
    where P: PartialOrd + Mul + Add + Sub +
             Clone + Copy + Default + Distance<P, Output = P> + 'a,
             &'a [P; K]: EuclideanDistance<&'a [P; K], Output = P> + 'a {
    pub fn new(positions:Rc<[P; K]>, value:Rc<RefCell<T>>) -> KDNode<'a, K,P,T> {
        KDNode {
            positions: positions,
            value: value,
            color: Rc::new(RefCell::new(Color::Red)),
            left: None,
            right: None,
            l:PhantomData::<&'a ()>
        }
    }

    fn with_color(positions:Rc<[P; K]>, value:Rc<RefCell<T>>, color:Rc<RefCell<Color>>) -> KDNode<'a, K,P,T> {
        KDNode {
            positions: positions,
            value: value,
            color: color,
            left: None,
            right: None,
            l:PhantomData::<&'a ()>
        }
    }

    pub fn right_rotate(t: KDNode<'a, K,P,T>) -> KDNode<'a, K,P,T> {
        match t.left {
            Some(left) => {
                KDNode {
                    positions: left.positions,
                    value: left.value,
                    color: left.color,
                    left: left.left,
                    right: Some(Box::new(KDNode {
                        positions: t.positions,
                        value: t.value,
                        color: t.color,
                        left: left.right,
                        right: t.right,
                        l:PhantomData::<&'a ()>
                    },)),
                    l:PhantomData::<&'a ()>
                }
            },
            None => t
        }
    }

    pub fn left_rotate(t: KDNode<'a, K,P,T>) -> KDNode<'a, K,P,T> {
        match t.right {
            Some(right) => {
                KDNode {
                    positions: right.positions,
                    value: right.value,
                    color: right.color,
                    right: right.right,
                    left: Some(Box::new(KDNode {
                        positions: t.positions,
                        value: t.value,
                        color: t.color,
                        right: right.left,
                        left: t.left,
                        l:PhantomData::<&'a ()>
                    })),
                    l:PhantomData::<&'a ()>
                }
            },
            None => t
        }
    }

    #[allow(dead_code)]
    fn left_and_right_rotate(mut t: KDNode<'a, K,P,T>) -> KDNode<'a, K,P,T> {
        match t.left.take() {
            None => {
                t
            },
            Some(left) => {
                t.left = Some(Box::new(Self::left_rotate(*left)));
                Self::right_rotate(t)
            }
        }
    }

    #[allow(dead_code)]
    fn right_and_left_rotate(mut t: KDNode<'a, K,P,T>) -> KDNode<'a, K,P,T> {
        match t.right.take() {
            None => {
                t
            },
            Some(right) => {
                t.right = Some(Box::new(Self::right_rotate(*right)));
                Self::left_rotate(t)
            }
        }
    }

    fn nearest(t: Option<&'a Box<KDNode<'a, K,P,T>>>,
               positions:&'a [P; K],
               mut distance:P,
               nearest_positions:&'a [P; K],
               current_value:&Rc<RefCell<T>>,
               demension:usize) -> Option<(P, &'a [P; K], Rc<RefCell<T>>)> {
        t.and_then(|t| {
            if positions[demension].partial_cmp(&t.positions[demension]).unwrap().is_lt() {
                if let Some(c) = t.left.as_ref() {
                    if let Some((d,p,v)) = Self::nearest(
                        Some(&c), positions, distance, nearest_positions, current_value, (demension + 1) % K) {
                        distance = d;

                        let d = positions.euclidean_distance(&t.positions);

                        let mut current_value = Rc::clone(&current_value);

                        let current_positons = if d.partial_cmp(&distance).unwrap().is_le() {
                            distance = d;
                            current_value = Rc::clone(&t.value);
                            t.positions.borrow()
                        } else {
                            p
                        };

                        if let Some(c) = t.right.as_ref() {
                            if distance.partial_cmp(&positions[demension].distance(&c.positions[demension])).unwrap().is_gt() {
                                Some((distance,current_positons,v))
                            } else {
                                Self::nearest(Some(&c),positions,distance,&current_positons,&current_value,(demension + 1) % K)
                            }
                        } else {
                            Some((distance,current_positons,v))
                        }
                    } else {
                        None
                    }
                } else {
                    let d = positions.euclidean_distance(&t.positions);
                    let mut current_value = Rc::clone(&current_value);

                    let current_positons = if d.partial_cmp(&distance).unwrap().is_le() {
                        distance = d;
                        current_value = Rc::clone(&t.value);
                        t.positions.borrow()
                    } else {
                        nearest_positions
                    };

                    Some((distance,current_positons,current_value))
                }
            } else {
                if let Some(c) = t.right.as_ref() {
                    if let Some((d,p,v)) = Self::nearest(
                        Some(&c),positions,distance,nearest_positions,current_value,(demension + 1) % K) {
                        distance = d;

                        let d = positions.euclidean_distance(&t.positions);
                        let mut current_value = Rc::clone(&current_value);

                        let current_positons = if d.partial_cmp(&distance).unwrap().is_le() {
                            distance = d;
                            current_value = Rc::clone(&t.value);
                            t.positions.borrow()
                        } else {
                            p
                        };

                        if let Some(c) = t.left.as_ref() {
                            if distance.partial_cmp(&positions[demension].distance(&c.positions[demension])).unwrap().is_gt() {
                               Some((distance,current_positons,v))
                            } else {
                                Self::nearest(Some(&c),positions,distance,&current_positons,&current_value,(demension + 1) % K)
                            }
                        } else {
                            Some((distance,current_positons,v))
                        }
                    } else {
                        None
                    }
                } else {
                    let d = positions.euclidean_distance(&t.positions);
                    let mut current_value = Rc::clone(&current_value);

                    let current_positons = if d.partial_cmp(&distance).unwrap().is_le() {
                        distance = d;
                        current_value = Rc::clone(&t.value);
                        t.positions.borrow()
                    } else {
                        nearest_positions
                    };

                    Some((distance,current_positons,current_value))
                }
            }
        })
    }

    fn insert(t: Option<Box<KDNode<'a, K,P,T>>>,
              positions:&Rc<[P; K]>,
              color:&Rc<RefCell<Color>>,
              parent_color:Option<Color>,
              lr:Option<LR>,
              value:Rc<RefCell<T>>,
              demension:usize) -> (KDNode<'a, K,P,T>, Balance) {
        match t {
            None if demension == K - 1 => {
                let b = if parent_color.map(|c| c == Color::Red).unwrap_or(false) {
                    Balance::Pre
                } else {
                    Balance::None
                };

                (KDNode::with_color(Rc::clone(positions), Rc::clone(&value),Rc::clone(color)),b)
            },
            None if demension == 0 => {
                let (n,b) = Self::insert(None,
                                         positions,
                                         &color,
                                         parent_color,
                                         None,
                                         Rc::clone(&value), (demension+1) % K);

                let t = KDNode {
                    positions: Rc::clone(positions),
                    value: Rc::clone(&value),
                    color: Rc::clone(&color),
                    left: None,
                    right: Some(Box::new(n)),
                    l:PhantomData::<&'a ()>
                };

                Self::balance(t,demension,b,lr,Some(LR::R))
            },
            None => {
                let (n,b) = Self::insert(None,
                                         positions,
                                         &Rc::clone(color),
                                         parent_color,
                                         lr,
                                         Rc::clone(&value), (demension+1) % K);

                let t = KDNode {
                    positions: Rc::clone(positions),
                    value: Rc::clone(&value),
                    color: Rc::clone(&color),
                    left: None,
                    right: Some(Box::new(n)),
                    l:PhantomData::<&'a ()>
                };

                Self::balance(t,demension,b,None,None)
            },
            Some(mut t) if demension == K - 1 => {
                let parent_color = Some(color.deref().borrow().clone());

                if positions[demension].partial_cmp(&t.positions[demension]).unwrap().is_lt() {
                    let (n,b) = Self::insert(t.left,
                                             positions,
                                             &Rc::clone(&t.color),
                                             parent_color,
                                             Some(LR::L),
                                             value, (demension+1) % K);

                    t.left = Some(Box::new(n));

                    (*t,b)
                } else {
                    let (n,b) = Self::insert(t.right,
                                             positions,
                                             &Rc::clone(&t.color),
                                             parent_color,
                                             Some(LR::R),
                                             value, (demension+1) % K);

                    t.right = Some(Box::new(n));

                    (*t,b)
                }
            },
            Some(mut t) if demension == 0 => {
                if positions[demension].partial_cmp(&t.positions[demension]).unwrap().is_lt() {
                    let (n,b) = Self::insert(t.left,
                                             positions,
                                             color,
                                             parent_color,
                                             lr,
                                             value, (demension+1) % K);

                    t.left = Some(Box::new(n));

                    if demension == 0 {
                        Self::balance(*t, demension, b, lr,Some(LR::L))
                    } else {
                        (*t,b)
                    }
                } else {
                    let (n,b) = Self::insert(t.right,
                                             positions,
                                             color,
                                             parent_color,
                                             lr,
                                             value, (demension+1) % K);

                    t.right = Some(Box::new(n));

                    if demension == 0 {
                        Self::balance(*t, demension, b, lr,Some(LR::R))
                    } else {
                        (*t,b)
                    }
                }
            },
            Some(mut t) => {
                if positions[demension].partial_cmp(&t.positions[demension]).unwrap().is_lt() {
                    let (n,b) = Self::insert(t.left,
                                             positions,
                                             color,
                                             parent_color,
                                             lr,
                                             value, (demension+1) % K);

                    t.left = Some(Box::new(n));

                    if demension == 0 {
                        Self::balance(*t, demension, b, lr,Some(LR::L))
                    } else {
                        (*t,b)
                    }
                } else {
                    let (n,b) = Self::insert(t.right,
                                             positions,
                                             color,
                                             parent_color,
                                             lr,
                                             value, (demension+1) % K);

                    t.right = Some(Box::new(n));

                    if demension == 0 {
                        Self::balance(*t, demension, b, lr,Some(LR::R))
                    } else {
                        (*t,b)
                    }
                }
            }
        }
    }

    fn balance(mut t: KDNode<'a, K,P,T>, demension:usize, balance:Balance, parent_lr:Option<LR>, lr:Option<LR>) -> (KDNode<'a, K,P,T>, Balance) {
        if demension > 0 {
            (t,balance)
        } else {
            match balance {
                Balance::None => (t, balance),
                Balance::Pre => {
                    let lr = lr.unwrap();
                    let parent_lr = parent_lr.unwrap();

                    for _ in 0..K {
                        t = if parent_lr != lr && lr == LR::L {
                            Self::right_rotate(t)
                        } else if parent_lr != lr && lr == LR::R {
                            Self::left_rotate(t)
                        } else {
                            t
                        };
                    }

                    (t,Balance::Fix)
                },
                Balance::Fix => {
                    let lr = lr.unwrap();

                    for _ in 0..K {
                        t = match lr {
                            LR::L => Self::right_rotate(t),
                            LR::R => Self::left_rotate(t)
                        };
                    }

                    match lr {
                        LR::L => {
                            if let Some(c) = t.left.as_ref() {
                                *c.color.borrow_mut() = Color::Black;
                            }
                        },
                        LR::R => {
                            if let Some(c) = t.right.as_ref() {
                                *c.color.borrow_mut() = Color::Black;
                            }
                        }
                    }
                    (t,Balance::None)
                }
            }
        }
    }
}
#[derive(Debug)]
pub struct KDTree<'a,const K:usize,P,T>
    where P: PartialOrd + Mul + Add + Sub + Clone + Copy + Default + Distance<P, Output = P> + 'a,
          &'a [P; K]: EuclideanDistance<&'a [P; K], Output = P> + 'a {
    root: Option<Box<KDNode<'a, K,P,T>>>,
    l:PhantomData<&'a ()>
}
impl<'a,const K:usize,P,T> KDTree<'a, K,P,T>
    where P: PartialOrd + Mul + Add + Sub + Clone + Copy + Default + Distance<P, Output = P> + 'a,
          &'a [P; K]: EuclideanDistance<&'a [P; K], Output = P> + 'a {
    pub fn new() -> KDTree<'a, K,P,T> {
        KDTree {
            root: None,
            l:PhantomData::<&'a ()>
        }
    }

    pub fn nearest(&'a self, positions:&'a [P; K]) -> Option<(&'a [P; K], Rc<RefCell<T>>)> {
        self.root.as_ref().and_then(|root| {
            let distance = positions.euclidean_distance(&root.positions);

            KDNode::nearest(Some(root),positions,distance,&root.positions,&root.value,0).map(|(_,p,v)| {
                (p,v)
            })
        })
    }

    pub fn nearest_position(&'a self, positions:&'a [P; K]) -> Option<&'a [P; K]> {
        self.root.as_ref().and_then(|root| {
            let distance = positions.euclidean_distance(&root.positions);

            KDNode::nearest(Some(root),positions,distance,&root.positions,&root.value,0).map(|(_,p,_)| {
                p
            })
        })
    }

    pub fn insert(&mut self, positions:[P; K], value:T) {
        let (n,_) = KDNode::insert(self.root.take(),
                                   &Rc::new(positions),
                                   &Rc::new(RefCell::new(Color::Black)),
                                   None,
                                   None,
                                   Rc::new(RefCell::new(value)),
                                   0);
        self.root = Some(Box::new(n));
        self.root.as_ref().map(|root| {
            *root.color.borrow_mut() = Color::Black;
        });
    }
}


