import 'package:flutter/material.dart';

class UserSubmissions extends StatelessWidget{
  final String image;

  const UserSubmissions({
    Key? key,
    required this.image,
  }) : super(key: key);

  @override
  Widget build(BuildContext context) {
    return GridView.count(
      primary: false,
      padding: const EdgeInsets.all(1),
      crossAxisSpacing: 10,
      mainAxisSpacing: 10,
      crossAxisCount: 2,
      shrinkWrap: true,
      children: <Widget>[
        Container(
          decoration: const BoxDecoration(
            image: DecorationImage(
              image: NetworkImage(
                  'https://i.guim.co.uk/img/media/3fa6fbb9f821db2c8c6973ee738d5e1cacb11df0/145_169_3211_1927/master/3211.jpg?width=1200&height=900&quality=85&auto=format&fit=crop&s=e93551f181ef7ab1c487fc316b33d27d'),
              fit: BoxFit.cover,
            ),
          ),
        ),
        Container(
          decoration: const BoxDecoration(
            image: DecorationImage(
              image: NetworkImage(
                  'https://i.guim.co.uk/img/media/3fa6fbb9f821db2c8c6973ee738d5e1cacb11df0/145_169_3211_1927/master/3211.jpg?width=1200&height=900&quality=85&auto=format&fit=crop&s=e93551f181ef7ab1c487fc316b33d27d'),
              fit: BoxFit.cover,
            ),
          ),
        ),
        Container(
          decoration: const BoxDecoration(
            image: DecorationImage(
              image: NetworkImage(
                  'https://i.guim.co.uk/img/media/3fa6fbb9f821db2c8c6973ee738d5e1cacb11df0/145_169_3211_1927/master/3211.jpg?width=1200&height=900&quality=85&auto=format&fit=crop&s=e93551f181ef7ab1c487fc316b33d27d'),
              fit: BoxFit.cover,
            ),
          ),
        ),
        Container(
          decoration: const BoxDecoration(
            image: DecorationImage(
              image: NetworkImage(
                  'https://i.guim.co.uk/img/media/3fa6fbb9f821db2c8c6973ee738d5e1cacb11df0/145_169_3211_1927/master/3211.jpg?width=1200&height=900&quality=85&auto=format&fit=crop&s=e93551f181ef7ab1c487fc316b33d27d'),
              fit: BoxFit.cover,
            ),
          ),
        ),
      ],
    );
  }
}