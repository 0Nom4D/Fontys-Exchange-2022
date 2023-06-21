import 'package:flutter/material.dart';

class UserWidget extends StatelessWidget{
  final String profileUrl;
  final String fullname;

  const UserWidget({
    Key? key,
    required this.profileUrl,
    required this.fullname,
  }) : super(key: key);

  @override
  Widget build(BuildContext context) {
    // This method creates the user widget composed by
    // user profile picture and fullname
    return Center(
      child: Column(
        children: [
          Image(image: AssetImage(profileUrl)),
          Container(
            decoration: const BoxDecoration(
              color: Colors.black,
            ),
            padding: const EdgeInsets.all(10),
            child: Text(
              fullname,
              style: const TextStyle(
                fontSize: 24,
                fontWeight: FontWeight.bold,
                fontStyle: FontStyle.italic,
                color: Colors.white,
              ),
            ),
          ),
        ],
      ),
    );
  }

}