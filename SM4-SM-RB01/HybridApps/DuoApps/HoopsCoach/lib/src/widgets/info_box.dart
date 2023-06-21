import 'package:flutter/material.dart';

class InfoBox extends StatelessWidget {
  const InfoBox({
    required this.title,
    required this.description,
    required this.icon,
    super.key
  });

  final String title;
  final String description;
  final IconData icon;

  @override
  Widget build(BuildContext context) {
    return Card(
      color: Colors.white.withOpacity(.23),
      elevation: 2.0,
      shape: RoundedRectangleBorder(
        borderRadius: BorderRadius.circular(15)
      ),
      child: Padding(
        padding: const EdgeInsets.all(8.0),
        child: Row(
          mainAxisAlignment: MainAxisAlignment.spaceAround,
          crossAxisAlignment: CrossAxisAlignment.center,
          children: [
            CircleAvatar(
              backgroundColor: Colors.white.withOpacity(.104),
              child: Icon(icon, color: Colors.white)
            ),
            const SizedBox(width: 5),
            Column(
              mainAxisAlignment: MainAxisAlignment.center,
              crossAxisAlignment: CrossAxisAlignment.center,
              children: [
                Text(title, style: const TextStyle(fontSize: 18, color: Colors.white)),
                const SizedBox(height: 10),
                Text(
                  description,
                  style: const TextStyle(
                    fontSize: 20,
                    fontWeight: FontWeight.bold,
                    color: Colors.white
                  )
                ),
              ],
            )
          ]
        ),
      ),
    );
  }
}
