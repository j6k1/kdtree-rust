use std::borrow::Borrow;
use std::cell::RefCell;
use std::cmp::Ordering;
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
#[derive(Debug)]
pub struct KDNode<'a,const D:usize,P,T> where P: PartialOrd +
                                              Mul<Output = P> + Add<Output = P> + Sub +
                                              Default + 'a,
                                              &'a P: Sub<&'a P, Output = P> {
    positions:Rc<[P;D]>,
    value:Rc<RefCell<T>>,
    color: Rc<RefCell<Color>>,
    left:Option<Box<KDNode<'a,D,P,T>>>,
    right:Option<Box<KDNode<'a,D,P,T>>>,
    l:PhantomData<&'a ()>
}
impl<'a,const D:usize,P,T> KDNode<'a,D,P,T> where P: PartialOrd +
                                                     Mul<Output = P> + Add<Output = P> + Sub +
                                                     Default + 'a,
                                                     &'a P: Sub<&'a P, Output = P> {
    pub fn new(positions:Rc<[P;D]>,value:Rc<RefCell<T>>) -> KDNode<'a,D,P,T> {
        KDNode {
            positions: positions,
            value: value,
            color: Rc::new(RefCell::new(Color::Red)),
            left: None,
            right: None,
            l:PhantomData::<&'a ()>
        }
    }

    pub fn right_rotate(t: KDNode<'a,D,P,T>) -> KDNode<'a,D,P,T> {
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

    pub fn left_rotate(t: KDNode<'a,D,P,T>) -> KDNode<'a,D,P,T> {
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
    fn left_and_right_rotate(mut t: KDNode<'a,D,P,T>) -> KDNode<'a,D,P,T> {
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
    fn right_and_left_rotate(mut t: KDNode<'a,D,P,T>) -> KDNode<'a,D,P,T> {
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

    fn nearest(t: Option<&'a Box<KDNode<'a,D,P,T>>>,
               positions:&'a [P;D],
               parent_positions:Option<&'a Rc<[P;D]>>,
               parent_value:Option<&'a Rc<RefCell<T>>>,
               demension:usize) -> Option<(&'a [P;D],Rc<RefCell<T>>)> {
        if let Some(t) = t {
            if positions[demension].partial_cmp(&t.positions[demension]).unwrap() == Ordering::Less {
                if let Some(c) = t.left.as_ref() {
                    Self::nearest(Some(&c),positions,Some(&c.positions),Some(&c.value),(demension + 1) % D)
                } else {
                    if demension == D - 1 {
                        if let Some(parent_positions) = parent_positions.as_ref() {
                            Some(Self::select(positions,
                                         t.positions.borrow(),
                                         &t.value,
                                         parent_positions,
                                                parent_value
                                        ))
                        } else {
                            Some((t.positions.borrow(),Rc::clone(&t.value)))
                        }
                    } else {
                        unreachable!()
                    }
                }
            } else {
                if let Some(c) = t.right.as_ref() {
                    Self::nearest(Some(&c),positions,Some(&c.positions),Some(&c.value),(demension + 1) % D)
                } else {
                    if demension == D - 1 {
                        if let Some(parent_positions) = parent_positions.as_ref() {
                            Some(Self::select(positions,
                                         t.positions.borrow(),
                                         &t.value,
                                         parent_positions,
                                         parent_value
                            ))
                        } else {
                            Some((t.positions.borrow(),Rc::clone(&t.value)))
                        }
                    } else {
                        unreachable!()
                    }
                }
            }
        } else {
            None
        }
    }

    fn select(positions:&'a [P;D],
                  child:&'a [P;D],
                  child_value:&'a Rc<RefCell<T>>,
                  parent:&'a [P;D],
                  parent_value:Option<&'a Rc<RefCell<T>>>) -> (&'a [P;D],Rc<RefCell<T>>) {
        let distance_child = positions.iter().zip(child.iter()).fold(P::default(),|acc,(p1,p2)| {
            acc + (p1 - p2) * (p1 - p2)
        });

        let distance_parent = positions.iter().zip(parent.iter()).fold(P::default(),|acc,(p1,p2)| {
            acc + (p1 - p2) * (p1 - p2)
        });

        if distance_child.partial_cmp(&distance_parent).unwrap() == Ordering::Less {
            (child,Rc::clone(child_value))
        } else {
            (parent,Rc::clone(parent_value.unwrap()))
        }
    }

    fn insert(t: Option<Box<KDNode<'a,D,P,T>>>,
              positions:&Rc<[P;D]>,
              parent_color:Option<Color>,
              lr:Option<LR>,
              value:Rc<RefCell<T>>,
              demension:usize) -> (KDNode<'a,D,P,T>,Balance) {
        match t {
            None if demension == D - 1 => {
                let b = if parent_color.map(|c| c == Color::Red).unwrap_or(false) {
                    Balance::Pre
                } else {
                    Balance::None
                };

                (KDNode::new(Rc::clone(positions), Rc::clone(&value)),b)
            },
            None => {
                let (n,b) = Self::insert(None,
                                         positions,
                                         None,
                                         None,
                                         Rc::clone(&value), (demension+1) % D);

                let t = KDNode {
                    positions: Rc::clone(positions),
                    value: Rc::clone(&value),
                    color: Rc::new(RefCell::new(Color::Red)),
                    left: None,
                    right: Some(Box::new(n)),
                    l:PhantomData::<&'a ()>
                };

                Self::balance(t,demension,b,None,None)
            },
            Some(mut t) if demension == D - 1 => {
                if positions[demension].partial_cmp(&t.positions[demension]).unwrap() == Ordering::Less {
                    let (n,b) = Self::insert(t.left,
                                             positions,
                                             Some(*t.color.deref().borrow()),
                                             Some(LR::L),
                                             value, (demension+1) % D);

                    t.left = Some(Box::new(n));

                    (*t,b)
                } else {
                    let (n,b) = Self::insert(t.right,
                                             positions,
                                             Some(*t.color.deref().borrow()),
                                             Some(LR::R),
                                             value, (demension+1) % D);

                    t.right = Some(Box::new(n));

                    (*t,b)
                }
            },
            Some(mut t) => {
                if positions[demension].partial_cmp(&t.positions[demension]).unwrap() == Ordering::Less {
                    let (n,b) = Self::insert(t.left,
                                             positions,
                                             parent_color,
                                             lr,
                                             value, (demension+1) % D);

                    t.left = Some(Box::new(n));

                    if demension == 0 {
                        Self::balance(*t, demension, b, lr,Some(LR::L))
                    } else {
                        (*t,b)
                    }
                } else {
                    let (n,b) = Self::insert(t.right,
                                             positions,
                                             parent_color,
                                             lr,
                                             value, (demension+1) % D);

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

    fn balance(mut t: KDNode<'a,D,P,T>,demension:usize,balance:Balance,parent_lr:Option<LR>,lr:Option<LR>) -> (KDNode<'a,D,P,T>,Balance) {
        if demension > 0 {
            (t,balance)
        } else {
            match balance {
                Balance::None => (t, balance),
                Balance::Pre => {
                    let lr = lr.unwrap();
                    let parent_lr = parent_lr.unwrap();

                    for _ in 0..D {
                        t = if parent_lr != lr && lr == LR::L {
                            Self::right_rotate(t)
                        } else if parent_lr != lr && lr == LR::R {
                            Self::left_rotate(t)
                        } else {
                            t
                        };
                    }

                    *t.color.borrow_mut() = Color::Black;

                    (t,Balance::Fix)
                },
                Balance::Fix => {
                    let lr = lr.unwrap();

                    for _ in 0..D {
                        t = match lr {
                            LR::L => Self::right_rotate(t),
                            LR::R => Self::left_rotate(t)
                        };
                    }

                    (t,Balance::None)
                }
            }
        }
    }
}
#[derive(Debug)]
pub struct KDTree<'a,const D:usize,P,T> where P: PartialOrd +
                                                 Mul<Output = P> + Add<Output = P> + Sub +
                                                 Default + 'a,
                                                 &'a P: Sub<&'a P, Output = P> {
    root: Option<Box<KDNode<'a,D,P,T>>>,
    l:PhantomData<&'a ()>
}
impl<'a,const D:usize,P,T> KDTree<'a,D,P,T> where P: PartialOrd +
                                                  Mul<Output = P> + Add<Output = P> + Sub +
                                                  Default + 'a,
                                                  &'a P: Sub<&'a P, Output = P> {
    pub fn new() -> KDTree<'a,D,P,T> {
        KDTree {
            root: None,
            l:PhantomData::<&'a ()>
        }
    }

    pub fn nearest(&'a self,positions:&'a [P;D]) -> Option<(&'a [P;D],Rc<RefCell<T>>)> {
        self.root.as_ref().and_then(|root| {
            KDNode::nearest(Some(root),positions,None,None,0)
        })
    }

    pub fn nearest_position(&'a self,positions:&'a [P;D]) -> Option<&'a [P;D]> {
        self.root.as_ref().and_then(|root| {
            KDNode::nearest(Some(root),positions,None,None,0).map(|(p,_)| {
                p
            })
        })
    }

    pub fn insert(&mut self,positions:[P;D],value:T) {
        let (n,_) = KDNode::insert(self.root.take(),
                                   &Rc::new(positions),
                                   None,
                                   None,
                                   Rc::new(RefCell::new(value)),
                                   0);
        self.root = Some(Box::new(n));
    }
}


