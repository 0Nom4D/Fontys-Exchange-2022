import 'package:flutter/material.dart';

class UserAwards extends StatelessWidget{
  final String award1;
  final String award2;

  const UserAwards({
    Key? key,
    required this.award1,
    required this.award2,
  }) : super(key: key);

  @override
  Widget build(BuildContext context) {
    return const Row(
      children: [
        Image(
          image: AssetImage('assets/images/Award1.png'),
          width: 50.0,
          height: 50.0,
        ),
        SizedBox(
          width: 16,
        ),
        Image(
          image: AssetImage('assets/images/Award2.png'),
          width: 50.0,
          height: 50.0,
        ),
      ],
    );
  }

}
