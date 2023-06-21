import 'package:flutter/material.dart';

class AlignedActionButton extends StatelessWidget {
  const AlignedActionButton({
    required this.label,
    required this.backgroundColor,
    required this.alignment,
    required this.callback,
    super.key
  });

  final String label;
  final Color backgroundColor;
  final Alignment alignment;
  final Future<void> Function() callback;

  @override
  Widget build(BuildContext context) {
    return Positioned.fill(
      child: Align(
        alignment: alignment,
        child: Padding(
          padding: const EdgeInsets.all(8.0),
          child: SizedBox(
            width: MediaQuery.of(context).size.width * .45,
            child: ElevatedButton(
              onPressed: callback,
              style: ElevatedButton.styleFrom(
                backgroundColor: backgroundColor
              ),
              child: Text(
                label.toUpperCase(),
                style: TextStyle(
                  color: Theme.of(context).colorScheme.onTertiary,
                  fontSize: 16
                ),
              )
            ),
          ),
        ),
      ),
    );
  }

}