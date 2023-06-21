import 'package:flutter/material.dart';

class UserActions extends StatelessWidget {
  final bool isLiked;
  final int likeNumber;
  final int commentNumber;
  final Function() onLike;
  final double fem;
  final double ffem;

  const UserActions({
    Key? key,
    required this.isLiked,
    required this.likeNumber,
    required this.commentNumber,
    required this.onLike,
    required this.fem,
    required this.ffem,
  }) : super(key: key);

  @override
  Widget build(BuildContext context) {
    return Row(
      children: [
        GestureDetector(
          onTap: onLike,
          child: Container(
          ),
        ),
        const SizedBox(
          child: Icon(
            Icons.more_horiz_outlined,
            size: 150,
            color: Color(0xffffffff),
          ),
        ),
      ],
    );
  }
}